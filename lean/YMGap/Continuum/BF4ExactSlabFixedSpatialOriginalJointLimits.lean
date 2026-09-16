/-
# Both original boundary iterated limits have the same joint limit

The cutoff-removed finite-chain expectation below is literally the existing
selected-face expectation at extent width+steps. Its time limit and the
cutoff limit of the already constructed boundaryTimeLimit are identified
with the SAME originalJointLimit by the rational rectangle estimate.

Outer thresholds and representative thresholds are explicit functions from
OriginalJointCauchy. The proof compares their existing representatives using
QMhat >= index; it constructs no new completion and chooses no representatives.
Nome, spatial width and physical source probe remain fixed. This is a
one-sided boundary joint limit, not a stationary law, bulk vacuum, reflected
OS state, continuum limit or width-uniform estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit (endpointInsertion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay (sourceProbeMassRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoundaryTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointCauchy
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation

/-- The already constructed original cutoff-removed selected-chain
expectation, at the literal ambient extent width+steps. -/
def originalCutoffExpectation {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (steps : Nat) : CReal :=
  expectation w hw0 hw1 (width+steps) (chainIds (width+steps) width 0 steps)
    (fun _ hi => chainIds_physical hi)
    (endpointInsertion (width+steps) 0 steps fs [])

/-- The inner cutoff limit is the original expectation, including its
original numerator and reciprocal partition normalization. -/
theorem originalCutoff_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor) (steps : Nat) :
    ConvergesTo (fun stage => ofQ' (originalTimeScalar hw0 hw1 width fs stage steps))
      (originalCutoffExpectation hw0 hw1 width fs steps) :=
  finite_converges w hw0 hw1 (width+steps) (chainIds (width+steps) width 0 steps)
    (fun _ hi => chainIds_physical hi)
    (endpointInsertion (width+steps) 0 steps fs [])

/-- Explicit comparison of existing representatives after cutoff removal.
The outer time threshold and both inner thresholds are displayed, and no
uniform finite-cutoff modulus in arbitrary time length is assumed. -/
theorem originalCutoffExpectation_approx_joint {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (steps a b : Nat)
    (hsteps : jointTimeThreshold hw0 hw1 width fs epsilon ≤ steps)
    (ha : jointCutoffThreshold hw0 hw1 width fs epsilon ≤ a)
    (hb : jointModulus hw0 hw1 width fs epsilon ≤ b) :
    (originalCutoffExpectation hw0 hw1 width fs steps).approx a ≤
        (originalJointLimit hw0 hw1 width fs hfs).approx b + epsilon ∧
      (originalJointLimit hw0 hw1 width fs hfs).approx b ≤
        (originalCutoffExpectation hw0 hw1 width fs steps).approx a + epsilon := by
  let c := finiteCauchy w hw0 hw1 (width+steps) (chainIds (width+steps) width 0 steps)
    (fun _ hi => chainIds_physical hi)
    (endpointInsertion (width+steps) 0 steps fs [])
  exact originalJoint_approx hw0 hw1 width fs hfs epsilon he
    (QMhat _ c a) steps b (Nat.le_trans ha (self_le_QMhat _ c a)) hsteps hb

/-- Remove the heat cutoff first, then send the opposite time boundary to
infinity: the limit is the constructed original joint limit. -/
theorem originalCutoffExpectation_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ConvergesTo (originalCutoffExpectation hw0 hw1 width fs)
      (originalJointLimit hw0 hw1 width fs hfs) := by
  intro epsilon he
  refine ⟨jointTimeThreshold hw0 hw1 width fs epsilon, fun steps hsteps =>
    ⟨jointModulus hw0 hw1 width fs epsilon, fun k hk => ?_⟩⟩
  exact originalCutoffExpectation_approx_joint hw0 hw1 width fs hfs epsilon he
    steps k k hsteps (Nat.le_trans (Nat.le_max_right _ _) hk) hk

/-- Explicit comparison after taking the existing time limit first. Its
representatives are pinned back to originalTimeScalar before applying the
same rectangle estimate. -/
theorem boundaryTimeLimit_approx_joint {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (stage a b : Nat)
    (hstage : jointCutoffThreshold hw0 hw1 width fs epsilon ≤ stage)
    (ha : jointTimeThreshold hw0 hw1 width fs epsilon ≤ a)
    (hb : jointModulus hw0 hw1 width fs epsilon ≤ b) :
    (boundaryTimeLimit hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) fs).approx a ≤
        (originalJointLimit hw0 hw1 width fs hfs).approx b + epsilon ∧
      (originalJointLimit hw0 hw1 width fs hfs).approx b ≤
        (boundaryTimeLimit hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) fs).approx a + epsilon := by
  let t := QMhat _ (boundaryTimeCauchy hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) fs) a
  have hr := originalJoint_approx hw0 hw1 width fs hfs epsilon he
    stage t b hstage (Nat.le_trans ha (self_le_QMhat _ _ a)) hb
  have hp := originalTimeScalar_pin hw0 hw1 width fs hfs stage t
  exact ⟨Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp) hr.1,
    Q'.le_trans' _ _ _ hr.2 (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hp))⟩

/-- Send the opposite time boundary to infinity first, then remove the heat
cutoff: the SAME original joint limit results. The outer cutoff threshold
and the shared representative threshold are the explicit parent functions. -/
theorem boundaryTimeLimit_converges_joint {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (fs : List FaceFactor)
    (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ConvergesTo (fun stage => boundaryTimeLimit hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) fs)
      (originalJointLimit hw0 hw1 width fs hfs) := by
  intro epsilon he
  refine ⟨jointCutoffThreshold hw0 hw1 width fs epsilon, fun stage hstage =>
    ⟨jointModulus hw0 hw1 width fs epsilon, fun k hk => ?_⟩⟩
  exact boundaryTimeLimit_approx_joint hw0 hw1 width fs hfs epsilon he
    stage k k hstage (Nat.le_trans (Nat.le_max_left _ _) hk) hk

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits.originalCutoffExpectation
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits.originalCutoff_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits.originalCutoffExpectation_approx_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits.originalCutoffExpectation_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits.boundaryTimeLimit_approx_joint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalJointLimits.boundaryTimeLimit_converges_joint
