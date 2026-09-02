/-
# Finite-atlas matching for the physical raw transport budget

The source-resolved physical covariance theorem exposes a candidate-dependent
score with two literal parts:

* the root/target/joint raw recoupling mismatch cost; and
* three copies of the pushed-law `remainderL1`.

This module selects a least-score positive coupling from any nonempty finite
atlas.  If the atlas lies in the proved strong-coupling coefficient corridor,
the selected physical block controls the fine covariance by its coarse anchor
plus that least score.  A listed reference candidate therefore transfers any
proved raw/total-variation estimate to the selected block.

The second score component is exactly three copies of the selected
candidate's own sign-observable matching defect by finite total-variation
duality.  Candidate dependence is retained throughout.

No atlas or refining-scale estimate is constructed here.  In particular,
finite minimization does not prove an `O(a)` estimate, projective consistency,
a continuum measure, OS/GNS reconstruction, or a physical mass gap.

Constructive contract: finite exact-rational computation and Type-valued
witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalRemainderL1DualObservable
import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackFubini
import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
import YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportMatchedStep

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualPhysicalRemainderL1DualObservable
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackFubini
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The candidate-dependent raw/total-variation score -/

/-- Raw mismatch plus three copies of the actual physical pushed-law `L1`
remainder at one positive candidate. -/
def physicalRawTransportBudgetAt
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Q' :=
  let S := G.block.candidateScalePair g hg candidate hcandidate
  let K := physicalKernel S rfl hcandidate
  let M := G.faceMap g hg candidate hcandidate
  physicalObservableRawMismatchCost S rfl hcandidate M +
    threePhysicalRemainderCost K

/-- The candidate-dependent sign-observable matching defect used to read the
total-variation component of the score observationally. -/
def physicalCandidateSignMatchBudgetAt
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Q' :=
  observableMatchDefect G.block g hg candidate hcandidate
    (physicalRemainderSignObservable G.block g hg candidate hcandidate)

/-- At each candidate, the observational sign-match budget is exactly the
physical pushed-law `L1` remainder appearing in the raw transport score. -/
theorem physicalCandidateSignMatchBudgetAt_eqv_remainderL1
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    physicalCandidateSignMatchBudgetAt G g hg candidate hcandidate ≈
      (physicalKernel
        (G.block.candidateScalePair g hg candidate hcandidate)
        rfl hcandidate).remainderL1 := by
  simpa only [physicalCandidateSignMatchBudgetAt] using
    physicalObservableMatchDefect_sign_eqv_remainderL1
      G.block g hg candidate hcandidate

/-- Atlas score.  Off-atlas values are irrelevant because the finite argmin
only selects and compares listed candidates. -/
def atlasPhysicalRawTransportScore
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    physicalRawTransportBudgetAt G g hg candidate
      (atlas.candidate_pos hcandidate)
  else 0

theorem atlasPhysicalRawTransportScore_of_mem
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    atlasPhysicalRawTransportScore G g hg atlas candidate =
      physicalRawTransportBudgetAt G g hg candidate
        (atlas.candidate_pos hcandidate) := by
  unfold atlasPhysicalRawTransportScore
  rw [dif_pos hcandidate]

/-! ## 2. Constructive finite selection -/

/-- The listed positive candidate with least actual raw/TV transport score. -/
@[irreducible] def physicalRawTransportMatchedCoupling
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) : Q' :=
  (finiteArgmin
    (atlasPhysicalRawTransportScore G g hg atlas)
    atlas.head atlas.tail).choice

theorem physicalRawTransportMatchedCoupling_mem
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    physicalRawTransportMatchedCoupling G g hg atlas ∈
      atlas.candidates := by
  unfold physicalRawTransportMatchedCoupling
  exact finiteArgmin_choice_mem
    (atlasPhysicalRawTransportScore G g hg atlas)
    atlas.head atlas.tail

theorem physicalRawTransportMatchedCoupling_pos
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    (0 : Q') < physicalRawTransportMatchedCoupling G g hg atlas :=
  atlas.candidate_pos
    (physicalRawTransportMatchedCoupling_mem G g hg atlas)

/-- The selected candidate is no worse than every listed reference candidate
for the literal candidate-dependent score. -/
theorem physicalRawTransportMatchedCoupling_minimizes
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    physicalRawTransportBudgetAt G g hg
        (physicalRawTransportMatchedCoupling G g hg atlas)
        (physicalRawTransportMatchedCoupling_pos G g hg atlas) ≤
      physicalRawTransportBudgetAt G g hg candidate
        (atlas.candidate_pos hcandidate) := by
  have hminimal :=
    finiteArgmin_minimal
      (atlasPhysicalRawTransportScore G g hg atlas)
      atlas.head atlas.tail candidate hcandidate
  have hchoiceEq :
      (finiteArgmin
        (atlasPhysicalRawTransportScore G g hg atlas)
        atlas.head atlas.tail).choice =
        physicalRawTransportMatchedCoupling G g hg atlas := by
    unfold physicalRawTransportMatchedCoupling
    rfl
  rw [hchoiceEq] at hminimal
  rw [
    atlasPhysicalRawTransportScore_of_mem G g hg atlas
      (physicalRawTransportMatchedCoupling G g hg atlas)
      (physicalRawTransportMatchedCoupling_mem G g hg atlas),
    atlasPhysicalRawTransportScore_of_mem G g hg atlas candidate hcandidate
  ] at hminimal
  exact hminimal

/-! ## 3. The selected physical block and reference comparison -/

def physicalRawTransportMatchedScalePair
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) : SlabScalePair :=
  G.block.candidateScalePair g hg
    (physicalRawTransportMatchedCoupling G g hg atlas)
    (physicalRawTransportMatchedCoupling_pos G g hg atlas)

def physicalRawTransportMatchedFaceMap
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    SlabFaceBlockMap
      (physicalRawTransportMatchedScalePair G g hg atlas) :=
  G.faceMap g hg
    (physicalRawTransportMatchedCoupling G g hg atlas)
    (physicalRawTransportMatchedCoupling_pos G g hg atlas)

def physicalRawTransportMatchedKernel
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    (physicalRawTransportMatchedScalePair G g hg atlas).FiniteSlabKernel :=
  physicalKernel
    (physicalRawTransportMatchedScalePair G g hg atlas) rfl
    (physicalRawTransportMatchedCoupling_pos G g hg atlas)

theorem physicalRawTransportMatchedCoupling_lt_one
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hlt : ∀ candidate, candidate ∈ atlas.candidates →
      candidate < (1 : Q')) :
    physicalRawTransportMatchedCoupling G g hg atlas < (1 : Q') :=
  hlt _ (physicalRawTransportMatchedCoupling_mem G g hg atlas)

theorem physicalRawTransportMatchedCoupling_coefficient
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hcoefficient : ∀ candidate, candidate ∈ atlas.candidates →
      exteriorFaceCoefficient candidate 0 ≤ anchorFaceCoefficient) :
    exteriorFaceCoefficient
        (physicalRawTransportMatchedCoupling G g hg atlas) 0 ≤
      anchorFaceCoefficient :=
  hcoefficient _
    (physicalRawTransportMatchedCoupling_mem G g hg atlas)

/-- The selected fine covariance is bounded by the selected coarse anchor plus
the least actual raw/total-variation score on the finite atlas. -/
theorem physicalRawTransportMatchedSlabFaceBooleanCovariance_le
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hlt : ∀ candidate, candidate ∈ atlas.candidates →
      candidate < (1 : Q'))
    (hcoefficient : ∀ candidate, candidate ∈ atlas.candidates →
      exteriorFaceCoefficient candidate 0 ≤ anchorFaceCoefficient) :
    let S := physicalRawTransportMatchedScalePair G g hg atlas
    let M := physicalRawTransportMatchedFaceMap G g hg atlas
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        physicalRawTransportBudgetAt G g hg
          (physicalRawTransportMatchedCoupling G g hg atlas)
          (physicalRawTransportMatchedCoupling_pos G g hg atlas) := by
  let selected := physicalRawTransportMatchedCoupling G g hg atlas
  let hselected := physicalRawTransportMatchedCoupling_pos G g hg atlas
  let S := physicalRawTransportMatchedScalePair G g hg atlas
  let M := physicalRawTransportMatchedFaceMap G g hg atlas
  let K := physicalRawTransportMatchedKernel G g hg atlas
  have hcentered :=
    cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_centeredBudget
      S rfl hselected M
      (physicalRawTransportMatchedCoupling_lt_one G g hg atlas hlt)
      (physicalRawTransportMatchedCoupling_coefficient
        G g hg atlas hcoefficient)
  have hpullback :
      centeredObservablePullbackDefect K M ≤
        physicalObservableRawMismatchCost S rfl hselected M := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centeredObservablePullbackDefect_eqv_abs_sourceAverage K M)) ?_
    refine Q'.le_trans' _ _ _
      (centeredObservablePullbackSourceRemainder_abs_le_mismatchCost K M) ?_
    exact Q'.le_of_eqv
      (observableSourcePullbackMismatchCost_physicalKernel_eqv_raw
        S rfl hselected M)
  have hremainder :
      centeredPhysicalRemainderDefect K M ≤
        threePhysicalRemainderCost K := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centeredPhysicalRemainderDefect_eqv_abs_centeredCylinderRemainder
          K M)) ?_
    exact centeredCylinderRemainder_abs_le_threePhysicalRemainderCost K M
  have hbudget :
      centeredPhysicalTransportBudget K M ≤
        physicalRawTransportBudgetAt G g hg selected hselected := by
    unfold centeredPhysicalTransportBudget physicalRawTransportBudgetAt
    exact Q'.add_le_add hpullback hremainder
  exact Q'.le_trans' _ _ _ hcentered
    (Q'.add_le_add_left _ _ _ hbudget)

/-- Any listed reference estimate transfers to the selected block.  The
remaining analytic task is to construct such a reference with an `O(a)`
score uniformly along the physical schedule. -/
theorem physicalRawTransportMatchedSlabFaceBooleanCovariance_le_reference
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hlt : ∀ candidate, candidate ∈ atlas.candidates →
      candidate < (1 : Q'))
    (hcoefficient : ∀ candidate, candidate ∈ atlas.candidates →
      exteriorFaceCoefficient candidate 0 ≤ anchorFaceCoefficient)
    (reference : Q') (hreference : reference ∈ atlas.candidates) :
    let S := physicalRawTransportMatchedScalePair G g hg atlas
    let M := physicalRawTransportMatchedFaceMap G g hg atlas
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        physicalRawTransportBudgetAt G g hg reference
          (atlas.candidate_pos hreference) := by
  have hselected :=
    physicalRawTransportMatchedSlabFaceBooleanCovariance_le
      G g hg atlas hlt hcoefficient
  exact Q'.le_trans' _ _ _ hselected
    (Q'.add_le_add_left _ _ _
      (physicalRawTransportMatchedCoupling_minimizes
        G g hg atlas reference hreference))

#print axioms physicalRawTransportBudgetAt
#print axioms physicalCandidateSignMatchBudgetAt_eqv_remainderL1
#print axioms physicalRawTransportMatchedCoupling_mem
#print axioms physicalRawTransportMatchedCoupling_pos
#print axioms physicalRawTransportMatchedCoupling_minimizes
#print axioms physicalRawTransportMatchedCoupling_lt_one
#print axioms physicalRawTransportMatchedCoupling_coefficient
#print axioms physicalRawTransportMatchedSlabFaceBooleanCovariance_le
#print axioms physicalRawTransportMatchedSlabFaceBooleanCovariance_le_reference

end YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportMatchedStep
