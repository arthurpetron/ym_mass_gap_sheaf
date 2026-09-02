/-
# Scale tail for the actual observable raw-transport budget

The exact cutoff-one physical-decimation theorem now ends at two literal
finite quantities:

* the positive-row average of globally glued raw mismatch ratios; and
* the absolute connected pushed-law cylinder remainder.

This module records the sharp unconditional normalization boundary and then
states the next physical input without hiding it.  Every kernel-row mismatch
mass is at most one, every averaged raw mismatch is at most one, and the
root/target/joint raw mismatch cost is at most three.  These bounds certify
normalization but are not small enough to prove contraction.

A `PhysicalObservableRefinementSchedule` attaches the exact construction to a
nested dyadic face geometry, a positive subunit fine nome, and a positive
lattice spacing tending to zero.  `LinearRawTransportTail` is the named open
analytic input that the sum of the actual raw mismatch cost and connected
pushed-law remainder is `O(a)`.  From an inhabitant, finite rational order
arithmetic computes a modulus and proves that the literal transport budget
tends to zero, then substitutes that result into the exact covariance theorem.

No `LinearRawTransportTail` inhabitant is constructed here.  In particular,
this file proves neither raw-ratio decay, pushed-law decay, projective
consistency, a continuum Yang--Mills measure, nor a physical mass gap.

Constructive contract: exact finite rational probability bounds and explicit
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservableDecimationPhysicalTransport
import YMGap.Continuum.PhysicalSeparatorLinearTail

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableDecimationPhysicalTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabObservablePhysicalTransportMatchedStep
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, h =>
      Q'.add_le_add
        (h head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => h item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Universal probability bounds for the actual raw mismatch -/

/-- Every literal mismatch event has mass at most one in a normalized kernel
row. -/
theorem kernelRowCylinderMismatchMass_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    kernelRowCylinderMismatchMass K fineEvent coarseEvent source ≤
      (1 : Q') := by
  unfold kernelRowCylinderMismatchMass
  exact finiteEventMass_le_one
    (K.kernel source) S.coarse.physicalLabellings
    (cylinderPullbackMismatchEvent fineEvent coarseEvent source)
    (fun target htarget => K.nonnegative source target hsource htarget)
    (K.row_normalized source hsource)

/-- A fine-law average of nonnegative row-mismatch masses is nonnegative. -/
theorem averagedCylinderPullbackMismatchMass_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    (0 : Q') ≤
      averagedCylinderPullbackMismatchMass K fineEvent coarseEvent := by
  unfold averagedCylinderPullbackMismatchMass
  apply listQSum_nonnegative_on
  intro source hsource
  exact Q'.mul_nonneg _ _
    (S.fine.normalizedMass_nonnegative source)
    (kernelRowCylinderMismatchMass_nonnegative
      K fineEvent coarseEvent source hsource)

/-- Averaging row probabilities against the normalized fine Gibbs law cannot
exceed one. -/
theorem averagedCylinderPullbackMismatchMass_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    averagedCylinderPullbackMismatchMass K fineEvent coarseEvent ≤
      (1 : Q') := by
  unfold averagedCylinderPullbackMismatchMass
  have hsum :
      listQSum
          (fun source =>
            S.fine.normalizedMass source *
              kernelRowCylinderMismatchMass K
                fineEvent coarseEvent source)
          S.fine.physicalLabellings ≤
        listQSum S.fine.normalizedMass
          S.fine.physicalLabellings := by
    apply listQSum_mono_local
    intro source hsource
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        (kernelRowCylinderMismatchMass K
          fineEvent coarseEvent source)
        1 (S.fine.normalizedMass source)
        (kernelRowCylinderMismatchMass_le_one
          K fineEvent coarseEvent source hsource)
        (S.fine.normalizedMass_nonnegative source)) ?_
    exact Q'.le_of_eqv
      (Q'.mul_one_eqv (S.fine.normalizedMass source))
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv S.fine.normalizedMass_total)

/-- The actual positive-row raw mismatch average is nonnegative. -/
theorem physicalRawMismatchAverage_nonnegative
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    (0 : Q') ≤
      physicalRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineEvent coarseEvent := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  have havg :=
    averagedCylinderPullbackMismatchMass_nonnegative
      K fineEvent coarseEvent
  have hraw :=
    averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
      S hfineCutoff hcoarseCoupling fineEvent coarseEvent
  exact Q'.le_trans' _ _ _ havg (Q'.le_of_eqv hraw)

/-- The selected raw numerator never exceeds its complete row denominator
after averaging over the fine Gibbs law. -/
theorem physicalRawMismatchAverage_le_one
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    physicalRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineEvent coarseEvent ≤ (1 : Q') := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  have havg :=
    averagedCylinderPullbackMismatchMass_le_one
      K fineEvent coarseEvent
  have hraw :=
    averagedCylinderPullbackMismatchMass_physicalKernel_eqv_raw
      S hfineCutoff hcoarseCoupling fineEvent coarseEvent
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hraw) havg

theorem physicalFaceRawMismatchAverage_nonnegative
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineFaceId coarseFaceId : Nat) :
    (0 : Q') ≤
      physicalFaceRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineFaceId coarseFaceId := by
  unfold physicalFaceRawMismatchAverage
  exact physicalRawMismatchAverage_nonnegative
    S hfineCutoff hcoarseCoupling _ _

theorem physicalFaceRawMismatchAverage_le_one
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineFaceId coarseFaceId : Nat) :
    physicalFaceRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineFaceId coarseFaceId ≤ (1 : Q') := by
  unfold physicalFaceRawMismatchAverage
  exact physicalRawMismatchAverage_le_one
    S hfineCutoff hcoarseCoupling _ _

theorem physicalFacePairRawMismatchAverage_nonnegative
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) :
    (0 : Q') ≤
      physicalFacePairRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineRoot fineTarget coarseRoot coarseTarget := by
  unfold physicalFacePairRawMismatchAverage
  exact physicalRawMismatchAverage_nonnegative
    S hfineCutoff hcoarseCoupling _ _

theorem physicalFacePairRawMismatchAverage_le_one
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) :
    physicalFacePairRawMismatchAverage S hfineCutoff hcoarseCoupling
        fineRoot fineTarget coarseRoot coarseTarget ≤ (1 : Q') := by
  unfold physicalFacePairRawMismatchAverage
  exact physicalRawMismatchAverage_le_one
    S hfineCutoff hcoarseCoupling _ _

theorem physicalObservableRawMismatchCost_nonnegative
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    (0 : Q') ≤
      physicalObservableRawMismatchCost
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalObservableRawMismatchCost
  exact Q'.zero_le_add _ _
    (physicalFacePairRawMismatchAverage_nonnegative
      S hfineCutoff hcoarseCoupling _ _ _ _)
    (Q'.zero_le_add _ _
      (physicalFaceRawMismatchAverage_nonnegative
        S hfineCutoff hcoarseCoupling _ _)
      (physicalFaceRawMismatchAverage_nonnegative
        S hfineCutoff hcoarseCoupling _ _))

/-- The unconditional root/target/joint normalization ceiling.  It is a
scorecard bound, not the refining-scale smallness estimate still required. -/
theorem physicalObservableRawMismatchCost_le_three
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalObservableRawMismatchCost
        S hfineCutoff hcoarseCoupling M ≤
      (1 : Q') + (1 + 1) := by
  unfold physicalObservableRawMismatchCost
  exact Q'.add_le_add
    (physicalFacePairRawMismatchAverage_le_one
      S hfineCutoff hcoarseCoupling _ _ _ _)
    (Q'.add_le_add
      (physicalFaceRawMismatchAverage_le_one
        S hfineCutoff hcoarseCoupling _ _)
      (physicalFaceRawMismatchAverage_le_one
        S hfineCutoff hcoarseCoupling _ _))

/-! ## 2. The exact scale-indexed physical schedule -/

/-- A nested dyadic family carrying the exact inputs consumed by the
physical-decimation theorem at every refining scale.  The geometric coherence
fields make the next block's coarse slab literally the current block's fine
slab.  No measure consistency or asymptotically-free law is inferred. -/
structure PhysicalObservableRefinementSchedule : Type where
  geometry : Nat → CutoffOneFaceGeometry
  fineCoupling : Nat → Q'
  fineCoupling_pos : ∀ scale, (0 : Q') < fineCoupling scale
  fineCoupling_lt_one : ∀ scale, fineCoupling scale < (1 : Q')
  spacing : PhysicalSpacing
  spacingToZero : SpacingToZero spacing
  coarseHalf_succ : ∀ scale,
    (geometry (scale + 1)).block.coarseHalf =
      (geometry scale).block.fineHalf
  coarseRoot_succ : ∀ scale,
    (geometry (scale + 1)).coarseRoot = (geometry scale).fineRoot
  coarseTarget_succ : ∀ scale,
    (geometry (scale + 1)).coarseTarget = (geometry scale).fineTarget

namespace PhysicalObservableRefinementSchedule

/-- Exact strong-coupling corridor nome selected from the fine nome. -/
def effectiveCoupling
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  observableDecimationCoupling (schedule.fineCoupling scale)

theorem effectiveCoupling_pos
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') < schedule.effectiveCoupling scale :=
  observableDecimationCoupling_pos (schedule.fineCoupling_pos scale)

/-- Literal cutoff-one/cutoff-four scale pair at one schedule index. -/
def scalePair
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : SlabScalePair :=
  (schedule.geometry scale).block.candidateScalePair
    (schedule.fineCoupling scale)
    (Q'.le_of_lt (schedule.fineCoupling_pos scale))
    (schedule.effectiveCoupling scale)
    (schedule.effectiveCoupling_pos scale)

/-- The face map on the same exact block and selected coupling. -/
def faceMap
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : SlabFaceBlockMap (schedule.scalePair scale) :=
  (schedule.geometry scale).faceMap
    (schedule.fineCoupling scale)
    (Q'.le_of_lt (schedule.fineCoupling_pos scale))
    (schedule.effectiveCoupling scale)
    (schedule.effectiveCoupling_pos scale)

/-- The globally link-glued physical kernel scored at this scale. -/
def kernel
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : (schedule.scalePair scale).FiniteSlabKernel :=
  physicalKernel (schedule.scalePair scale) rfl
    (schedule.effectiveCoupling_pos scale)

/-- Fine literal face covariance at one schedule index. -/
def fineCovariance
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  slabPhysicalFaceBooleanCovariance
    (schedule.scalePair scale).fine
    (schedule.faceMap scale).fineRoot
    (schedule.faceMap scale).fineTarget

/-- Already-proved coarse strong-coupling anchor at one schedule index. -/
def anchorRate
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  slabObservablePairedSupportGlobalAnchorRate
    (schedule.scalePair scale).coarse
    (schedule.faceMap scale).coarseRoot
    (schedule.faceMap scale).coarseTarget

/-- The exact remaining physical transport payment: actual raw mismatch plus
the absolute connected pushed-law cylinder remainder. -/
def rawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  physicalObservableRawMismatchCost
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale) +
    Q'.abs
      (centeredCylinderRemainder
        (schedule.kernel scale) (schedule.faceMap scale))

theorem rawTransportBudget_nonnegative
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    (0 : Q') ≤ schedule.rawTransportBudget scale := by
  unfold rawTransportBudget
  exact Q'.zero_le_add _ _
    (physicalObservableRawMismatchCost_nonnegative
      (schedule.scalePair scale) rfl
      (schedule.effectiveCoupling_pos scale)
      (schedule.faceMap scale))
    (Q'.abs_nonneg _)

/-- Per-scale exact-decimation theorem, with no unnamed error terms. -/
theorem fineCovariance_le_anchorRate_add_rawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + schedule.rawTransportBudget scale := by
  simpa only [fineCovariance, anchorRate, rawTransportBudget, scalePair,
      faceMap, kernel, effectiveCoupling] using
    observableDecimationPhysicalRawMismatchTransport_covariance_le
      (schedule.geometry scale)
      (schedule.fineCoupling scale)
      (schedule.fineCoupling_pos scale)
      (schedule.fineCoupling_lt_one scale)

/-! ## 3. Honest vanishing and physical-linear tail inputs -/

/-- Direct constructive modulus for the actual transport budget.  This is an
input surface, not an inhabited theorem about the current physical kernel. -/
structure RawTransportBudgetToZero
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  modulus : Q' → Nat
  budget_le : ∀ epsilon : Q', (0 : Q') < epsilon →
    ∀ scale : Nat, modulus epsilon ≤ scale →
      schedule.rawTransportBudget scale ≤ epsilon

/-- Eventual exact covariance control from a supplied vanishing budget. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (schedule : PhysicalObservableRefinementSchedule)
    (vanishing : RawTransportBudgetToZero schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : vanishing.modulus epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon := by
  exact Q'.le_trans' _ _ _
    (schedule.fineCovariance_le_anchorRate_add_rawTransportBudget scale)
    (Q'.add_le_add_left _ _ _
      (vanishing.budget_le epsilon hepsilon scale hscale))

/-- The substantive physical tail input: after `start`, the complete literal
transport budget is bounded linearly by the same positive lattice spacing
carried by the refinement schedule.  No inhabitant is supplied. -/
structure LinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  budget_le : ∀ scale : Nat, start ≤ scale →
    schedule.rawTransportBudget scale ≤
      ceiling * schedule.spacing.spacing scale

namespace LinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Positive spacing threshold that makes the linear transport payment at
most `epsilon`. -/
def spacingThreshold
    (tail : LinearRawTransportTail schedule)
    (epsilon : Q') : Q' :=
  Q'.divPos epsilon tail.ceiling tail.ceiling_pos

theorem spacingThreshold_pos
    (tail : LinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < tail.spacingThreshold epsilon :=
  Q'.divPos_pos epsilon tail.ceiling tail.ceiling_pos hepsilon

/-- Explicit common index beyond both the analytic tail start and the spacing
modulus at the required threshold. -/
def eventualStart
    (tail : LinearRawTransportTail schedule)
    (epsilon : Q') : Nat :=
  max tail.start
    (schedule.spacingToZero.modulus (tail.spacingThreshold epsilon))

theorem ceiling_mul_spacingThreshold_eqv
    (tail : LinearRawTransportTail schedule)
    (epsilon : Q') :
    tail.ceiling * tail.spacingThreshold epsilon ≈ epsilon := by
  unfold spacingThreshold
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv tail.ceiling
      (Q'.divPos epsilon tail.ceiling tail.ceiling_pos))
    (Q'.divPos_mul_eqv epsilon tail.ceiling tail.ceiling_pos)

/-- Linear-in-spacing physical control supplies a constructive vanishing
modulus for the complete actual transport budget. -/
theorem rawTransportBudget_le_epsilon
    (tail : LinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : tail.eventualStart epsilon ≤ scale) :
    schedule.rawTransportBudget scale ≤ epsilon := by
  have hstart : tail.start ≤ scale :=
    Nat.le_trans (Nat.le_max_left _ _) hscale
  have hmodulus :
      schedule.spacingToZero.modulus
          (tail.spacingThreshold epsilon) ≤ scale :=
    Nat.le_trans (Nat.le_max_right _ _) hscale
  have hspacing :
      schedule.spacing.spacing scale ≤
        tail.spacingThreshold epsilon :=
    schedule.spacingToZero.spacing_le
      (tail.spacingThreshold epsilon)
      (tail.spacingThreshold_pos epsilon hepsilon)
      scale hmodulus
  have hscaled :
      tail.ceiling * schedule.spacing.spacing scale ≤
        tail.ceiling * tail.spacingThreshold epsilon :=
    Q'.mul_le_mul_of_nonneg_left _ _ tail.ceiling hspacing
      (Q'.le_of_lt tail.ceiling_pos)
  exact Q'.le_trans' _ _ _ (tail.budget_le scale hstart)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (tail.ceiling_mul_spacingThreshold_eqv epsilon)))

/-- Forget the stronger `O(a)` statement while retaining its computed
modulus. -/
def toRawTransportBudgetToZero
    (tail : LinearRawTransportTail schedule) :
    RawTransportBudgetToZero schedule where
  modulus := tail.eventualStart
  budget_le := fun epsilon hepsilon scale hscale =>
    tail.rawTransportBudget_le_epsilon
      epsilon hepsilon scale hscale

/-- Final consumer at this finite/refining interface: the actual covariance
is eventually bounded by the proved coarse anchor plus arbitrary positive
rational error. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : LinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat) (hscale : tail.eventualStart epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  PhysicalObservableRefinementSchedule.fineCovariance_le_anchorRate_add_epsilon
    schedule tail.toRawTransportBudgetToZero
    epsilon hepsilon scale hscale

end LinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms kernelRowCylinderMismatchMass_le_one
#print axioms averagedCylinderPullbackMismatchMass_nonnegative
#print axioms averagedCylinderPullbackMismatchMass_le_one
#print axioms physicalRawMismatchAverage_nonnegative
#print axioms physicalRawMismatchAverage_le_one
#print axioms physicalObservableRawMismatchCost_nonnegative
#print axioms physicalObservableRawMismatchCost_le_three
#print axioms PhysicalObservableRefinementSchedule
#print axioms PhysicalObservableRefinementSchedule.rawTransportBudget_nonnegative
#print axioms PhysicalObservableRefinementSchedule.fineCovariance_le_anchorRate_add_rawTransportBudget
#print axioms PhysicalObservableRefinementSchedule.RawTransportBudgetToZero
#print axioms PhysicalObservableRefinementSchedule.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.LinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.LinearRawTransportTail.rawTransportBudget_le_epsilon
#print axioms PhysicalObservableRefinementSchedule.LinearRawTransportTail.toRawTransportBudgetToZero
#print axioms PhysicalObservableRefinementSchedule.LinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
