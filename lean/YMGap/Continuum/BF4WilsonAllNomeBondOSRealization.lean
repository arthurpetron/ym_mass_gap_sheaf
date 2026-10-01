/-
# The original bond-reflected form in the witnessed time sector

The constructed square root of the SAME transfer realizes the physical odd
Wilson-window form. Its null relation is exactly equality of the realized
vectors. Every original time-sector state has computed dense bond-source
approximants and is their existing completed limit, with explicit moduli.

This is a fixed-nome, fixed-width bond-reflection realization. The ambient
carrier and its nonzero time kernel remain intact; only the actual physical
bond form regards those inputs as null. No continuum OS root, multiplier
invariance, spatial scaling or physical mass claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm
import YMGap.Continuum.BF4WilsonAllNomeRootTimeRange
import YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedTime_embed)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub completedSub_embed)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root root_sub root_zero_depth)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
  (root_pairing root_square root_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeRootTimeRange (rootRange)
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
  (rootRepresentative rootRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (quarter quarter_positive four_quarters)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State CauchySequence)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "R" => root hw0 hw1 1
local notation "E" => embed hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- This form is defined by the ORIGINAL reflected joint limit, not by a
new Gram functional declared physical without an identification theorem. -/
def bondForm (x y : IntrinsicExpression width) : RC :=
  Quotient.mk crealSetoid
    (originalJointLimit hw0 hw1 (2*(max x.radius y.radius)+1)
      (crossOdd x y) (crossOdd_within x y))

/-- Actual image with a computed original time-range witness. -/
def image (x : IntrinsicExpression width) : State hw0 hw1 (width := width) where
  val := R (E x)
  range := rootRange hw0 hw1 1 ((D).constant x)

/-- The physical bond-reflection pairing is the original sector pairing. -/
theorem image_pairing (x y : IntrinsicExpression width) :
    B (image hw0 hw1 x).val (image hw0 hw1 y).val = bondForm hw0 hw1 x y := by
  change B (R (E x)) (R (E y)) = _
  rw [root_pairing hw0 hw1 0, root_zero_depth]
  exact completed_crossOdd_pin hw0 hw1 x y

/-- Exact physical seminorm of a difference, including all signed terms. -/
theorem image_distance (x y : IntrinsicExpression width) :
    dist (image hw0 hw1 x).val (image hw0 hw1 y).val =
      bondForm hw0 hw1 (difference x y) (difference x y) := by
  change B (completedSub hw0 hw1 (R (E x)) (R (E y)))
    (completedSub hw0 hw1 (R (E x)) (R (E y))) = _
  rw [← root_sub, completedSub_embed]
  exact image_pairing hw0 hw1 (difference x y) (difference x y)

/-- Precisely the physical bond null relation is identified. This does not
identify the original ambient time kernel with ambient zero. -/
theorem image_eq_iff_bond_null (x y : IntrinsicExpression width) :
    (image hw0 hw1 x).val = (image hw0 hw1 y).val ↔
      bondForm hw0 hw1 (difference x y) (difference x y) = RCzero := by
  rw [← image_distance]
  exact (completedDist_zero_iff hw0 hw1 _ _).symm

/-- A dense source is bond-null exactly when its ORIGINAL transfer image
vanishes. The source need not have zero norm in the ambient carrier. -/
theorem bond_null_iff_time_kernel (x : IntrinsicExpression width) :
    bondForm hw0 hw1 x x = RCzero ↔
      T 1 (E x) = BF4WilsonAllNomeLinear.completedZero hw0 hw1 width := by
  rw [← image_pairing]
  change B (R (E x)) (R (E x)) = RCzero ↔ _
  exact (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width (R (E x))).trans
    (BF4WilsonAllNomeNestedRootCompatibility.root_zero_iff_time_zero hw0 hw1 1 (E x))

private theorem root_time (x : V) : R (T 1 x) = T 1 (R x) := by
  have hs (z : V) : R (R z) = T 1 z := by
    rw [root_square hw0 hw1 0, root_zero_depth]
  exact (congrArg R (hs x).symm).trans (hs (R x))

/-- The physical one-step advance intertwines the SAME completed transfer. -/
theorem image_advance (x : IntrinsicExpression width) :
    (image hw0 hw1 (advance 1 x)).val = T 1 (image hw0 hw1 x).val := by
  change R (E (advance 1 x)) = T 1 (R (E x))
  rw [← completedTime_embed]
  exact root_time hw0 hw1 (E x)

/-- The bond realization retains the already constructed normalized vacuum. -/
theorem image_unit :
    (image hw0 hw1 (unit width)).val = unitState hw0 hw1 width := by
  change R (unitState hw0 hw1 width) = unitState hw0 hw1 width
  exact BF4WilsonAllNomePositiveTimeVacuum.meshAction_unit hw0 hw1 1 1

/-- Two constructive approximations: first use the state's given T-range
witness, then sample the explicit square-root representative of its preimage.
The input preimages need no uniform bound and need not converge. -/
def denseExpression (x : State hw0 hw1 (width := width)) (epsilon : Q') :
    IntrinsicExpression width :=
  let X := x.range.preimage (x.range.modulus (quarter epsilon))
  let Y := rootRepresentative hw0 hw1 1 X
  Y.seq (Y.modulus (quarter epsilon))

/-- Every sector vector has an actual finite signed Wilson source within
the requested squared-distance tolerance in the physical bond form. -/
theorem denseExpression_bound (x : State hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (dist (image hw0 hw1 (denseExpression hw0 hw1 x epsilon)).val x.val)
      (rat epsilon) := by
  let delta := quarter epsilon
  have hd : (0 : Q') < delta := quarter_positive he
  let X := x.range.preimage (x.range.modulus delta)
  let Y := rootRepresentative hw0 hw1 1 X
  have hnear := CRealSeminormCompletedApproximation.constantApproximation_bound
    (distanceData hw0 hw1) Y delta hd (Y.modulus delta) (Nat.le_refl _)
  change RCle (dist (E (Y.seq (Y.modulus delta))) (Class Y)) (rat delta) at hnear
  have hfirst := RCle_trans
    (root_distance_bound hw0 hw1 1 (E (Y.seq (Y.modulus delta))) (Class Y)) hnear
  have hroot : R (Class Y) = T 1 (Class X) := by
    dsimp only [Y]
    rw [rootRepresentative_pin, root_square hw0 hw1 0, root_zero_depth]
  rw [hroot] at hfirst
  have hsecond := x.range.bound delta hd (x.range.modulus delta) (Nat.le_refl _)
  have h := RCle_trans
    (completedDist_triangle hw0 hw1 (R (E (Y.seq (Y.modulus delta))))
      (T 1 (Class X)) x.val)
    (RCadd_le_add (RCadd_le_add hfirst hfirst) (RCadd_le_add hsecond hsecond))
  rw [four_quarters] at h
  exact h

/-- A fixed explicit precision schedule of ORIGINAL finite expressions. -/
def denseSequence (x : State hw0 hw1 (width := width)) (n : Nat) :
    IntrinsicExpression width := denseExpression hw0 hw1 x (Q'.invSucc n)

theorem denseSequence_bound (x : State hw0 hw1 (width := width))
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat) (hn : epsilon.den ≤ n) :
    RCle (dist (image hw0 hw1 (denseSequence hw0 hw1 x n)).val x.val)
      (rat epsilon) :=
  RCle_trans (denseExpression_bound hw0 hw1 x (Q'.invSucc n) (Q'.invSucc_pos n))
    (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hn) (HalfPow.invSucc_den_le epsilon he)))

/-- The actual dense images are Cauchy with a computed all-tail modulus. -/
def denseRows (x : State hw0 hw1 (width := width)) :
    CauchySequence hw0 hw1 (width := width) where
  seq := fun n => image hw0 hw1 (denseSequence hw0 hw1 x n)
  modulus := fun epsilon => (quarter epsilon).den
  bound := by
    intro epsilon he m n hm hn
    have hd := quarter_positive he
    have hl := denseSequence_bound hw0 hw1 x (quarter epsilon) hd m hm
    have hr := denseSequence_bound hw0 hw1 x (quarter epsilon) hd n hn
    rw [completedDist_symm] at hr
    have h := RCle_trans (completedDist_triangle hw0 hw1 _ x.val _)
      (RCadd_le_add (RCadd_le_add hl hl) (RCadd_le_add hr hr))
    rwa [four_quarters] at h

/-- No additional sector vectors are missed by completing the physical bond
images: the computed limit recovers EVERY existing witnessed sector state. -/
theorem dense_limit (x : State hw0 hw1 (width := width)) :
    (BF4WilsonAllNomeTimeSector.limit hw0 hw1 (denseRows hw0 hw1 x)).val = x.val :=
  BF4WilsonAllNomeTimeSector.limit_unique hw0 hw1 (denseRows hw0 hw1 x) x.val
    (fun epsilon => epsilon.den) (denseSequence_bound hw0 hw1 x)

#print axioms bondForm
#print axioms image
#print axioms image_pairing
#print axioms image_distance
#print axioms image_eq_iff_bond_null
#print axioms bond_null_iff_time_kernel
#print axioms image_advance
#print axioms image_unit
#print axioms denseExpression
#print axioms denseExpression_bound
#print axioms denseSequence_bound
#print axioms denseRows
#print axioms dense_limit

end YMGap.Continuum.BF4WilsonAllNomeBondOSRealization
