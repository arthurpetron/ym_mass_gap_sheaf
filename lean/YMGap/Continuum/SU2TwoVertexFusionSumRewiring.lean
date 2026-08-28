/-
# Rewiring and additive collisions on a two-vertex SU(2) chain

The canonical left-fusion chain at valence four has two trivalent vertices
joined by one same-slot internal edge.  The unit resolutions from the local
continuation obstruction give two accepted colored path systems:

* `ca ; ca` pairs external legs `0` and `3`;
* `bc ; ab` pairs external legs `1` and `2`.

After componentwise addition, canonical re-resolution and same-slot
continuation instead pair `0` with `2` and `1` with `3`.  Thus local support
union does not imply union of physical terminal pairings.

Moreover, the alternative decomposition `ca ; ab` and `bc ; ca` already has
the latter two pairings, while its two summed resolutions are equal to the
first output.  The local additive compiler therefore has an explicit
collision: crossed sums alone do not retain the source decomposition.

This does not yet instantiate the complete corrected-slab switch carrier;
other links or retained global provenance might separate the two inputs.  It
does refute a decoder proof that uses only vertexwise addition, canonical
same-slot continuation, and the resulting local summed assignments.

Constructive contract: literal finite ports, exact local mates, and
resolution uniqueness only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, or noncomputable declaration.
-/

import YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction

namespace YMGap.Continuum.SU2TwoVertexFusionSumRewiring

set_option autoImplicit false

open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.SU2TrivalentStrandPortContinuationObstruction
open YMGap.Continuum.SU2TrivalentStrandResolutionAddition

/-! ## 1. External leg identifiers for the two-vertex chain -/

/-- At the first vertex, `a` and `b` are external positions zero and one;
`c` is the internal edge. -/
def firstVertexEdgeId : TrivalentLeg → Nat
  | .a => 0
  | .b => 1
  | .c => 5

/-- At the second vertex, `a` is the same internal edge and `b`,`c` are
external positions two and three. -/
def secondVertexEdgeId : TrivalentLeg → Nat
  | .a => 5
  | .b => 2
  | .c => 3

/-! ## 2. The first colored decomposition -/

def sourceA_leftFirstStart : TrivalentStrandPort 1 0 1 :=
  .onA ⟨0, by omega⟩

def sourceA_leftFirstMate : TrivalentStrandPort 1 0 1 :=
  strandMate unitCAResolution sourceA_leftFirstStart

def sourceA_leftSecondIncoming : TrivalentStrandPort 1 0 1 :=
  .onA ⟨sourceA_leftFirstMate.slot, by
    change 0 < 1
    omega⟩

def sourceA_leftFinish : TrivalentStrandPort 1 0 1 :=
  strandMate unitCAResolution sourceA_leftSecondIncoming

theorem sourceA_left_path :
    firstVertexEdgeId sourceA_leftFirstStart.leg = 0 ∧
      sourceA_leftFirstMate.leg = .c ∧
      sourceA_leftFirstMate.slot = sourceA_leftSecondIncoming.slot ∧
      secondVertexEdgeId sourceA_leftFinish.leg = 3 := by
  decide

def sourceA_rightFirstStart : TrivalentStrandPort 0 1 1 :=
  .onB ⟨0, by omega⟩

def sourceA_rightFirstMate : TrivalentStrandPort 0 1 1 :=
  strandMate unitBCResolution sourceA_rightFirstStart

def sourceA_rightSecondIncoming : TrivalentStrandPort 1 1 0 :=
  .onA ⟨sourceA_rightFirstMate.slot, by
    change 0 < 1
    omega⟩

def sourceA_rightFinish : TrivalentStrandPort 1 1 0 :=
  strandMate unitABResolution sourceA_rightSecondIncoming

theorem sourceA_right_path :
    firstVertexEdgeId sourceA_rightFirstStart.leg = 1 ∧
      sourceA_rightFirstMate.leg = .c ∧
      sourceA_rightFirstMate.slot = sourceA_rightSecondIncoming.slot ∧
      secondVertexEdgeId sourceA_rightFinish.leg = 2 := by
  decide

/-! ## 3. Canonical addition rewires the physical endpoints -/

abbrev summedFirstResolution : TrivalentStrandResolution 1 1 2 :=
  addTrivalentStrandResolutions unitCAResolution unitBCResolution

abbrev summedSecondResolution : TrivalentStrandResolution 2 1 1 :=
  addTrivalentStrandResolutions unitCAResolution unitABResolution

def summedFromZeroFirstStart : TrivalentStrandPort 1 1 2 :=
  .onA ⟨0, by omega⟩

def summedFromZeroFirstMate : TrivalentStrandPort 1 1 2 :=
  strandMate summedFirstResolution summedFromZeroFirstStart

def summedFromZeroSecondIncoming : TrivalentStrandPort 2 1 1 :=
  .onA ⟨summedFromZeroFirstMate.slot, by
    change 1 < 2
    omega⟩

def summedFromZeroFinish : TrivalentStrandPort 2 1 1 :=
  strandMate summedSecondResolution summedFromZeroSecondIncoming

theorem summed_path_zero_to_two :
    firstVertexEdgeId summedFromZeroFirstStart.leg = 0 ∧
      summedFromZeroFirstMate.leg = .c ∧
      summedFromZeroFirstMate.slot = summedFromZeroSecondIncoming.slot ∧
      secondVertexEdgeId summedFromZeroFinish.leg = 2 := by
  decide

def summedFromOneFirstStart : TrivalentStrandPort 1 1 2 :=
  .onB ⟨0, by omega⟩

def summedFromOneFirstMate : TrivalentStrandPort 1 1 2 :=
  strandMate summedFirstResolution summedFromOneFirstStart

def summedFromOneSecondIncoming : TrivalentStrandPort 2 1 1 :=
  .onA ⟨summedFromOneFirstMate.slot, by
    change 0 < 2
    omega⟩

def summedFromOneFinish : TrivalentStrandPort 2 1 1 :=
  strandMate summedSecondResolution summedFromOneSecondIncoming

theorem summed_path_one_to_three :
    firstVertexEdgeId summedFromOneFirstStart.leg = 1 ∧
      summedFromOneFirstMate.leg = .c ∧
      summedFromOneFirstMate.slot = summedFromOneSecondIncoming.slot ∧
      secondVertexEdgeId summedFromOneFinish.leg = 3 := by
  decide

/-- The summed partner of external leg zero is not its partner in the left
source summand. -/
theorem summed_zero_partner_ne_sourceA_left_partner :
    secondVertexEdgeId summedFromZeroFinish.leg ≠
      secondVertexEdgeId sourceA_leftFinish.leg := by
  decide

/-! ## 4. A second decomposition has the same additive output -/

/-- The alternative colored decomposition exchanges the two second-vertex
resolutions.  It has paths `0--2` and `1--3`. -/
def alternativeSummedSecondResolution : TrivalentStrandResolution 2 1 1 :=
  addTrivalentStrandResolutions unitABResolution unitCAResolution

/-- Resolution uniqueness identifies the two additive outputs even though
their left/right second-vertex provenance is reversed. -/
theorem alternativeSummedSecondResolution_eq :
    alternativeSummedSecondResolution = summedSecondResolution :=
  TrivalentStrandResolution.unique _ _

/-- A two-point carrier for the two distinct colored decompositions. -/
inductive TwoVertexDecomposition : Type
  | sourceA
  | sourceB
  deriving DecidableEq

/-- Retain only the pair of summed local resolutions produced by the
additive compiler. -/
def twoVertexAdditiveOutput : TwoVertexDecomposition →
    TrivalentStrandResolution 1 1 2 ×
      TrivalentStrandResolution 2 1 1
  | .sourceA => (summedFirstResolution, summedSecondResolution)
  | .sourceB => (summedFirstResolution, alternativeSummedSecondResolution)

theorem twoVertexAdditiveOutput_collision :
    twoVertexAdditiveOutput .sourceA =
      twoVertexAdditiveOutput .sourceB := by
  unfold twoVertexAdditiveOutput
  rw [alternativeSummedSecondResolution_eq]

/-- **Local decoder obstruction.**  The additive output alone is not
injective on the two colored source decompositions. -/
theorem twoVertexAdditiveOutput_not_injective :
    ¬ Function.Injective twoVertexAdditiveOutput := by
  intro hinjective
  have heq := hinjective twoVertexAdditiveOutput_collision
  cases heq

end YMGap.Continuum.SU2TwoVertexFusionSumRewiring

#print axioms YMGap.Continuum.SU2TwoVertexFusionSumRewiring.sourceA_left_path
#print axioms YMGap.Continuum.SU2TwoVertexFusionSumRewiring.sourceA_right_path
#print axioms YMGap.Continuum.SU2TwoVertexFusionSumRewiring.summed_path_zero_to_two
#print axioms YMGap.Continuum.SU2TwoVertexFusionSumRewiring.summed_path_one_to_three
#print axioms YMGap.Continuum.SU2TwoVertexFusionSumRewiring.summed_zero_partner_ne_sourceA_left_partner
#print axioms YMGap.Continuum.SU2TwoVertexFusionSumRewiring.twoVertexAdditiveOutput_not_injective
