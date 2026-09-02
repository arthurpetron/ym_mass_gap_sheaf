/-
# A transport-matched physical block step for the literal slab covariance

The exact physical blocking-defect theorem exposes two computed errors for
the actual cutoff-one whole-slab Markov kernel: local observable pullback
distortion and the pushed-law/coarse-Gibbs remainder.  This module makes the
next coupling choice depend on that exact budget.

For a witness-bearing fine/coarse face geometry and a finite positive coupling
atlas, every candidate is scored by

  observablePullbackDefect + threePhysicalRemainderCost.

A constructive finite argmin selects the physical coarse coupling with least
score.  If every atlas entry lies in the already-proved coefficient corridor,
the selected actual block step controls the original fine face covariance by
the coarse global decay rate plus that least exact transport budget.

This is a trajectory-selection theorem, not a small-error theorem.  The
remaining analytic producer is to construct refining corridor atlases whose
selected budget is absorbable in block depth or observable separation.

Constructive contract: finite exact-rational computation only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4ObservableMatchedOneStep
import YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Candidate-independent face geometry -/

/-- Fine/coarse face coordinates for one cutoff-one dyadic slab block.

The membership witnesses depend only on the two geometric extents, so the
same four coordinates can be compared at every candidate coarse coupling.
-/
structure CutoffOneFaceGeometry : Type where
  block : CutoffOneGeometry
  fineRoot : Nat
  fineTarget : Nat
  coarseRoot : Nat
  coarseTarget : Nat
  fineRoot_mem :
    fineRoot ∈ slabPhysicalFaceEdges (centralExtent block.fineHalf)
  fineTarget_mem :
    fineTarget ∈ slabPhysicalFaceEdges (centralExtent block.fineHalf)
  coarseRoot_mem :
    coarseRoot ∈ slabPhysicalFaceEdges (centralExtent block.coarseHalf)
  coarseTarget_mem :
    coarseTarget ∈ slabPhysicalFaceEdges (centralExtent block.coarseHalf)

namespace CutoffOneFaceGeometry

/-- Rebuild the common face map at a supplied positive candidate coupling. -/
def faceMap
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    SlabFaceBlockMap
      (G.block.candidateScalePair g hg candidate hcandidate) where
  fineRoot := G.fineRoot
  fineTarget := G.fineTarget
  coarseRoot := G.coarseRoot
  coarseTarget := G.coarseTarget
  fineRoot_mem := G.fineRoot_mem
  fineTarget_mem := G.fineTarget_mem
  coarseRoot_mem := G.coarseRoot_mem
  coarseTarget_mem := G.coarseTarget_mem

@[simp] theorem faceMap_fineRoot
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    (G.faceMap g hg candidate hcandidate).fineRoot = G.fineRoot :=
  rfl

@[simp] theorem faceMap_fineTarget
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    (G.faceMap g hg candidate hcandidate).fineTarget = G.fineTarget :=
  rfl

@[simp] theorem faceMap_coarseRoot
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    (G.faceMap g hg candidate hcandidate).coarseRoot = G.coarseRoot :=
  rfl

@[simp] theorem faceMap_coarseTarget
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    (G.faceMap g hg candidate hcandidate).coarseTarget = G.coarseTarget :=
  rfl

end CutoffOneFaceGeometry

/-! ## 2. Exact physical transport score and finite argmin -/

/-- The exact covariance-transport budget at one positive candidate. -/
def physicalTransportBudgetAt
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Q' :=
  let S := G.block.candidateScalePair g hg candidate hcandidate
  let K := physicalKernel S rfl hcandidate
  let M := G.faceMap g hg candidate hcandidate
  observablePullbackDefect K M + threePhysicalRemainderCost K

/-- Total atlas score.  Off-atlas values are irrelevant because the finite
argmin can only select and compare listed candidates. -/
def atlasPhysicalTransportScore
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') : Q' :=
  if hcandidate : candidate ∈ atlas.candidates then
    physicalTransportBudgetAt G g hg candidate
      (atlas.candidate_pos hcandidate)
  else 0

theorem atlasPhysicalTransportScore_of_mem
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    atlasPhysicalTransportScore G g hg atlas candidate =
      physicalTransportBudgetAt G g hg candidate
        (atlas.candidate_pos hcandidate) := by
  unfold atlasPhysicalTransportScore
  rw [dif_pos hcandidate]

/-- The candidate whose actual physical kernel has least exact transport
budget on the supplied finite atlas. -/
def physicalTransportMatchedCoupling
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) : Q' :=
  (finiteArgmin
    (atlasPhysicalTransportScore G g hg atlas)
    atlas.head atlas.tail).choice

theorem physicalTransportMatchedCoupling_mem
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    physicalTransportMatchedCoupling G g hg atlas ∈
      atlas.candidates := by
  exact finiteArgmin_choice_mem
    (atlasPhysicalTransportScore G g hg atlas)
    atlas.head atlas.tail

theorem physicalTransportMatchedCoupling_pos
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    (0 : Q') < physicalTransportMatchedCoupling G g hg atlas :=
  atlas.candidate_pos
    (physicalTransportMatchedCoupling_mem G g hg atlas)

/-- The selected candidate minimizes the full exact transport budget, not a
surrogate observable score. -/
theorem physicalTransportMatchedCoupling_minimizes
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (candidate : Q') (hcandidate : candidate ∈ atlas.candidates) :
    physicalTransportBudgetAt G g hg
        (physicalTransportMatchedCoupling G g hg atlas)
        (physicalTransportMatchedCoupling_pos G g hg atlas) ≤
      physicalTransportBudgetAt G g hg candidate
        (atlas.candidate_pos hcandidate) := by
  have hminimal :=
    finiteArgmin_minimal
      (atlasPhysicalTransportScore G g hg atlas)
      atlas.head atlas.tail candidate hcandidate
  change
    atlasPhysicalTransportScore G g hg atlas
        (physicalTransportMatchedCoupling G g hg atlas) ≤
      atlasPhysicalTransportScore G g hg atlas candidate at hminimal
  rw [
    atlasPhysicalTransportScore_of_mem G g hg atlas
      (physicalTransportMatchedCoupling G g hg atlas)
      (physicalTransportMatchedCoupling_mem G g hg atlas),
    atlasPhysicalTransportScore_of_mem G g hg atlas candidate hcandidate
  ] at hminimal
  exact hminimal

/-! ## 3. The selected physical step and covariance theorem -/

def physicalTransportMatchedScalePair
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) : SlabScalePair :=
  G.block.candidateScalePair g hg
    (physicalTransportMatchedCoupling G g hg atlas)
    (physicalTransportMatchedCoupling_pos G g hg atlas)

def physicalTransportMatchedFaceMap
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    SlabFaceBlockMap
      (physicalTransportMatchedScalePair G g hg atlas) :=
  G.faceMap g hg
    (physicalTransportMatchedCoupling G g hg atlas)
    (physicalTransportMatchedCoupling_pos G g hg atlas)

def physicalTransportMatchedKernel
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    (physicalTransportMatchedScalePair G g hg atlas).FiniteSlabKernel :=
  physicalKernel
    (physicalTransportMatchedScalePair G g hg atlas)
    rfl
    (physicalTransportMatchedCoupling_pos G g hg atlas)

@[simp] theorem physicalTransportMatchedScalePair_coupling
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas) :
    (physicalTransportMatchedScalePair G g hg atlas).coarse.coupling =
      physicalTransportMatchedCoupling G g hg atlas :=
  rfl

/-- Every selected transport-matched coupling inherits an atlas-wide strict
upper bound. -/
theorem physicalTransportMatchedCoupling_lt_one
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hlt : ∀ candidate, candidate ∈ atlas.candidates →
      candidate < (1 : Q')) :
    physicalTransportMatchedCoupling G g hg atlas < (1 : Q') :=
  hlt _ (physicalTransportMatchedCoupling_mem G g hg atlas)

/-- Every selected transport-matched coupling inherits the atlas-wide
coefficient-corridor certificate. -/
theorem physicalTransportMatchedCoupling_coefficient
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hcoefficient : ∀ candidate, candidate ∈ atlas.candidates →
      exteriorFaceCoefficient candidate 0 ≤ anchorFaceCoefficient) :
    exteriorFaceCoefficient
        (physicalTransportMatchedCoupling G g hg atlas) 0 ≤
      anchorFaceCoefficient :=
  hcoefficient _ (physicalTransportMatchedCoupling_mem G g hg atlas)

/-- The actual transport-matched block step controls the original fine
literal covariance by the proved coarse rate plus the minimum exact budget
over the supplied corridor atlas. -/
theorem physicalTransportMatchedSlabFaceBooleanCovariance_le
    (G : CutoffOneFaceGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (atlas : PositiveCouplingAtlas)
    (hlt : ∀ candidate, candidate ∈ atlas.candidates →
      candidate < (1 : Q'))
    (hcoefficient : ∀ candidate, candidate ∈ atlas.candidates →
      exteriorFaceCoefficient candidate 0 ≤ anchorFaceCoefficient) :
    let S := physicalTransportMatchedScalePair G g hg atlas
    let M := physicalTransportMatchedFaceMap G g hg atlas
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        physicalTransportBudgetAt G g hg
          (physicalTransportMatchedCoupling G g hg atlas)
          (physicalTransportMatchedCoupling_pos G g hg atlas) := by
  let S := physicalTransportMatchedScalePair G g hg atlas
  let M := physicalTransportMatchedFaceMap G g hg atlas
  have hbase :=
    cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_transportBudget
      S rfl (physicalTransportMatchedCoupling_pos G g hg atlas) M
      (physicalTransportMatchedCoupling_lt_one G g hg atlas hlt)
      (physicalTransportMatchedCoupling_coefficient
        G g hg atlas hcoefficient)
  exact hbase

#print axioms physicalTransportBudgetAt
#print axioms physicalTransportMatchedCoupling_mem
#print axioms physicalTransportMatchedCoupling_pos
#print axioms physicalTransportMatchedCoupling_minimizes
#print axioms physicalTransportMatchedScalePair_coupling
#print axioms physicalTransportMatchedCoupling_lt_one
#print axioms physicalTransportMatchedCoupling_coefficient
#print axioms physicalTransportMatchedSlabFaceBooleanCovariance_le

end YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep
