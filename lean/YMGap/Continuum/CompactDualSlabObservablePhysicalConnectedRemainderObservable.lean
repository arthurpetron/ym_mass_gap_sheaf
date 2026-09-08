/-
# The connected pushed-law remainder as one bounded observable defect

The exact centered pushed-law remainder is a signed combination of the
joint, root, and target cylinder remainders.  This module packages that
combination as one explicit candidate-dependent coarse observable.  Its
blocked-minus-coarse expectation is exactly the connected remainder, and
the observable is pointwise bounded in absolute value by one.

Thus the sharp connected transport producer is an ordinary bounded
observable-matching estimate for a concrete three-cylinder observable.  No
smallness estimate is asserted here; in particular, boundedness alone does
not imply refining-scale decay, continuum consistency, OS/GNS
reconstruction, or a physical mass gap.

Constructive contract: finite rational sums, Boolean case splits, and exact
kernel identities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.BF4ObservableMatchedOneStep
import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem add_then_sub_left_local (left residual : Q') :
    (left + residual) + (-left) ≈ residual := by
  refine Q'.eqv_trans _
    (left + (residual + (-left))) _
    (Q'.add_assoc_eqv left residual (-left)) ?_
  refine Q'.eqv_trans _
    (left + ((-left) + residual)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.add_comm_eqv residual (-left))
  refine Q'.eqv_trans _
    ((left + (-left)) + residual) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv left (-left) residual)
  refine Q'.eqv_trans _ (0 + residual) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ residual
      (Q'.add_neg_self_eqv left)
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

/-! ## 1. Generic finite-kernel observable decomposition -/

/-- Expectation of a rational coarse observable under the signed physical
pushforward remainder. -/
def remainderObservableExpectation
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') : Q' :=
  observableExpectation K.remainder S.coarse.physicalLabellings observable

/-- Every coarse observable, not only the total-variation sign, obeys the
exact blocked = coarse + remainder expectation decomposition. -/
theorem blockedObservableExpectation_eqv_coarse_add_remainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') :
    observableExpectation K.blockedMass S.coarse.physicalLabellings
        observable ≈
      observableExpectation S.coarse.normalizedMass
          S.coarse.physicalLabellings observable +
        remainderObservableExpectation K observable := by
  unfold observableExpectation remainderObservableExpectation
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (S.coarse.normalizedMass target + K.remainder target) *
          observable target)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun target _ =>
        Q'.mul_eqv_congr_right _ _ (observable target)
          (K.pushforward_decomposition target))
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        S.coarse.normalizedMass target * observable target +
          K.remainder target * observable target)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun target _ =>
        Q'.add_mul_eqv
          (S.coarse.normalizedMass target)
          (K.remainder target) (observable target))
  exact listQSum_add
    (fun target => S.coarse.normalizedMass target * observable target)
    (fun target => K.remainder target * observable target)
    S.coarse.physicalLabellings

/-- The corresponding blocked-minus-coarse observable difference is exactly
the signed remainder expectation. -/
theorem blocked_sub_coarseObservableExpectation_eqv_remainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') :
    observableExpectation K.blockedMass S.coarse.physicalLabellings
          observable +
        -(observableExpectation S.coarse.normalizedMass
          S.coarse.physicalLabellings observable) ≈
      remainderObservableExpectation K observable := by
  let blocked := observableExpectation K.blockedMass
    S.coarse.physicalLabellings observable
  let coarse := observableExpectation S.coarse.normalizedMass
    S.coarse.physicalLabellings observable
  let residual := remainderObservableExpectation K observable
  refine Q'.eqv_trans _ ((coarse + residual) + (-coarse)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-coarse)
      (blockedObservableExpectation_eqv_coarse_add_remainder K observable)
  exact add_then_sub_left_local coarse residual

/-! ## 2. The explicit connected observable -/

/-- A cylinder indicator carrying an arbitrary rational coefficient. -/
def weightedCylinderObservable
    (event : SlabLabelling → Bool) (coefficient : Q')
    (state : SlabLabelling) : Q' :=
  if event state then coefficient else 0

/-- The signed-remainder expectation of a weighted cylinder is exactly its
cylinder remainder times the coefficient. -/
theorem weightedCylinderRemainderExpectation_eqv
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (event : SlabLabelling → Bool) (coefficient : Q') :
    remainderObservableExpectation K
        (weightedCylinderObservable event coefficient) ≈
      PhysicalKernel.cylinderRemainder K event * coefficient := by
  unfold remainderObservableExpectation observableExpectation
    weightedCylinderObservable PhysicalKernel.cylinderRemainder
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if event state then K.remainder state else 0) * coefficient)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun state _ => by
        cases hevent : event state
        · simp only [Bool.false_eq_true, if_false]
          exact Q'.eqv_trans _ 0 _
            (Q'.mul_zero_eqv (K.remainder state))
            (Q'.eqv_symm (Q'.zero_mul_eqv coefficient))
        · simp only [if_true]
          exact Q'.eqv_refl _)
  exact listQSum_mul_const
    (fun state => if event state then K.remainder state else 0)
    coefficient S.coarse.physicalLabellings

/-- The concrete three-cylinder observable whose expectation defect retains
the covariance centering cancellation. -/
def connectedRemainderObservable
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (state : SlabLabelling) : Q' :=
  weightedCylinderObservable
      (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)
      (-1) state +
    (weightedCylinderObservable
        (slabPhysicalFacePositiveB M.coarseRoot)
        (blockedFaceMoment K M.coarseTarget) state +
      weightedCylinderObservable
        (slabPhysicalFacePositiveB M.coarseTarget)
        (coarseFaceMoment K M.coarseRoot) state)

private theorem remainderObservableExpectation_add
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (left right : SlabLabelling → Q') :
    remainderObservableExpectation K (fun state => left state + right state) ≈
      remainderObservableExpectation K left +
        remainderObservableExpectation K right := by
  unfold remainderObservableExpectation observableExpectation
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        K.remainder state * left state + K.remainder state * right state)
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ S.coarse.physicalLabellings
      (fun state _ => Q'.mul_add_eqv
        (K.remainder state) (left state) (right state))
  exact listQSum_add
    (fun state => K.remainder state * left state)
    (fun state => K.remainder state * right state)
    S.coarse.physicalLabellings

/-- The signed remainder expectation of the connected observable is exactly
the centered cylinder remainder. -/
theorem connectedRemainderExpectation_eqv_centeredCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    remainderObservableExpectation K (connectedRemainderObservable K M) ≈
      centeredCylinderRemainder K M := by
  let pairObservable := weightedCylinderObservable
    (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget) (-1)
  let rootObservable := weightedCylinderObservable
    (slabPhysicalFacePositiveB M.coarseRoot)
    (blockedFaceMoment K M.coarseTarget)
  let targetObservable := weightedCylinderObservable
    (slabPhysicalFacePositiveB M.coarseTarget)
    (coarseFaceMoment K M.coarseRoot)
  have houter := remainderObservableExpectation_add K pairObservable
    (fun state => rootObservable state + targetObservable state)
  have hinner := remainderObservableExpectation_add K rootObservable
    targetObservable
  refine Q'.eqv_trans _
    (remainderObservableExpectation K pairObservable +
      (remainderObservableExpectation K rootObservable +
        remainderObservableExpectation K targetObservable)) _ ?_ ?_
  · unfold connectedRemainderObservable pairObservable rootObservable
      targetObservable
    exact Q'.eqv_trans _ _ _ houter
      (Q'.add_eqv_congr_left _ _ _ hinner)
  refine Q'.eqv_trans _
    (facePairCylinderRemainder K M.coarseRoot M.coarseTarget * (-1) +
      (faceCylinderRemainder K M.coarseRoot *
          blockedFaceMoment K M.coarseTarget +
        faceCylinderRemainder K M.coarseTarget *
          coarseFaceMoment K M.coarseRoot)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (weightedCylinderRemainderExpectation_eqv K _ (-1))
      (Q'.add_eqv_congr'
        (weightedCylinderRemainderExpectation_eqv K _
          (blockedFaceMoment K M.coarseTarget))
        (weightedCylinderRemainderExpectation_eqv K _
          (coarseFaceMoment K M.coarseRoot)))
  unfold centeredCylinderRemainder faceCylinderRemainder
    facePairCylinderRemainder
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _
      (Q'.mul_neg_eqv
        (PhysicalKernel.cylinderRemainder K
          (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)) 1)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_one_eqv
          (PhysicalKernel.cylinderRemainder K
            (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)))))
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.mul_comm_eqv
        (PhysicalKernel.cylinderRemainder K
          (slabPhysicalFacePositiveB M.coarseTarget))
        (coarseFaceMoment K M.coarseRoot)))

/-! ## 3. Exact defect identity and pointwise unit bound -/

/-- Absolute blocked/coarse defect for a rational observable under one
finite physical kernel. -/
def finiteKernelObservableMatchDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') : Q' :=
  Q'.abs
    (observableExpectation K.blockedMass S.coarse.physicalLabellings observable +
      -(observableExpectation S.coarse.normalizedMass
        S.coarse.physicalLabellings observable))

/-- The exact connected remainder budget is precisely the matching defect of
the structured connected observable. -/
theorem connectedObservableMatchDefect_eqv_abs_centeredCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    finiteKernelObservableMatchDefect K (connectedRemainderObservable K M) ≈
      Q'.abs (centeredCylinderRemainder K M) := by
  unfold finiteKernelObservableMatchDefect
  exact Q'.abs_eqv_congr
    (Q'.eqv_trans _ _ _
      (blocked_sub_coarseObservableExpectation_eqv_remainder K
        (connectedRemainderObservable K M))
      (connectedRemainderExpectation_eqv_centeredCylinderRemainder K M))

/-- The connected observable is pointwise bounded by one.  The joint case
uses both face-moment unit bounds; the other three Boolean cases reduce to a
single probability or zero. -/
theorem connectedRemainderObservable_abs_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (state : SlabLabelling) :
    Q'.abs (connectedRemainderObservable K M state) ≤ (1 : Q') := by
  have hblockedNonnegative :=
    blockedFaceMoment_nonnegative K M.coarseTarget
  have hblockedLeOne :=
    blockedFaceMoment_le_one K M.coarseTarget
  have hcoarseNonnegative :=
    coarseFaceMoment_nonnegative K M.coarseRoot
  have hcoarseLeOne :=
    coarseFaceMoment_le_one K M.coarseRoot
  cases hroot : slabPhysicalFacePositiveB M.coarseRoot state <;>
      cases htarget : slabPhysicalFacePositiveB M.coarseTarget state
  · simp only [connectedRemainderObservable, weightedCylinderObservable,
      slabPhysicalFacePairPositiveB, hroot, htarget, Bool.false_and,
      Bool.false_eq_true, if_false, Q'.zero_add']
    decide
  · simp only [connectedRemainderObservable, weightedCylinderObservable,
      slabPhysicalFacePairPositiveB, hroot, htarget, Bool.false_and,
      Bool.false_eq_true, if_false, if_true, Q'.zero_add']
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hcoarseNonnegative]
    exact hcoarseLeOne
  · simp only [connectedRemainderObservable, weightedCylinderObservable,
      slabPhysicalFacePairPositiveB, hroot, htarget, Bool.true_and,
      Bool.false_eq_true, if_false, if_true, Q'.zero_add', Q'.add_zero']
    rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hblockedNonnegative]
    exact hblockedLeOne
  · simp only [connectedRemainderObservable, weightedCylinderObservable,
      slabPhysicalFacePairPositiveB, hroot, htarget, Bool.true_and,
      if_true]
    apply Q'.abs_le
    · have hsumNonnegative :
          (0 : Q') ≤ blockedFaceMoment K M.coarseTarget +
            coarseFaceMoment K M.coarseRoot :=
        Q'.zero_le_add _ _ hblockedNonnegative hcoarseNonnegative
      have hadd := Q'.add_le_add_left
        (-1) 0
        (blockedFaceMoment K M.coarseTarget +
          coarseFaceMoment K M.coarseRoot)
        hsumNonnegative
      exact Q'.le_trans' _ _ _ (by decide) hadd
    · have hsumLeTwo :
          blockedFaceMoment K M.coarseTarget +
              coarseFaceMoment K M.coarseRoot ≤
            (1 : Q') + 1 :=
        Q'.add_le_add hblockedLeOne hcoarseLeOne
      have hadd := Q'.add_le_add_left
        (-1)
        (blockedFaceMoment K M.coarseTarget +
          coarseFaceMoment K M.coarseRoot)
        ((1 : Q') + 1) hsumLeTwo
      exact Q'.le_trans' _ _ _ hadd (by decide)

private theorem remainderObservableList_abs_le_l1
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q') :
    ∀ states : List SlabLabelling,
      (∀ state, state ∈ states → Q'.abs (observable state) ≤ (1 : Q')) →
      Q'.abs
          (listQSum
            (fun state => K.remainder state * observable state) states) ≤
        listQSum (fun state => Q'.abs (K.remainder state)) states
  | [], _ => by
      change Q'.abs (0 : Q') ≤ (0 : Q')
      decide
  | head :: tail, hbound => by
      simp only [listQSum]
      have hhead :
          Q'.abs (K.remainder head * observable head) ≤
            Q'.abs (K.remainder head) := by
        refine Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le (K.remainder head) (observable head)) ?_
        refine Q'.le_trans' _
          (Q'.abs (K.remainder head) * 1) _ ?_ ?_
        · exact Q'.mul_le_mul_of_nonneg_left
            (Q'.abs (observable head)) 1
            (Q'.abs (K.remainder head))
            (hbound head List.mem_cons_self)
            (Q'.abs_nonneg (K.remainder head))
        exact Q'.le_of_eqv
          (Q'.mul_one_eqv (Q'.abs (K.remainder head)))
      have htail := remainderObservableList_abs_le_l1 K observable tail
        (fun state hstate =>
          hbound state (List.mem_cons_of_mem head hstate))
      exact Q'.le_trans' _ _ _
        (Q'.abs_add_le'
          (K.remainder head * observable head)
          (listQSum
            (fun state => K.remainder state * observable state) tail))
        (Q'.add_le_add hhead htail)

/-- Any pointwise-unit-bounded coarse observable has signed-remainder
expectation at most the physical `L1` remainder. -/
theorem remainderObservableExpectation_abs_le_remainderL1
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : SlabLabelling → Q')
    (hbound : ∀ state, state ∈ S.coarse.physicalLabellings →
      Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs (remainderObservableExpectation K observable) ≤
      K.remainderL1 := by
  unfold remainderObservableExpectation observableExpectation
    SlabScalePair.FiniteSlabKernel.remainderL1
  exact remainderObservableList_abs_le_l1 K observable
    S.coarse.physicalLabellings hbound

/-- The three-cylinder cancellation improves the previous universal factor
three: the exact connected remainder is bounded by one copy of `remainderL1`.
This is still only a majorant, not a proof that either side is small. -/
theorem centeredCylinderRemainder_abs_le_remainderL1
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    Q'.abs (centeredCylinderRemainder K M) ≤ K.remainderL1 := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (Q'.eqv_symm
          (connectedRemainderExpectation_eqv_centeredCylinderRemainder
            K M)))) ?_
  exact remainderObservableExpectation_abs_le_remainderL1 K
    (connectedRemainderObservable K M)
    (fun state _ => connectedRemainderObservable_abs_le_one K M state)

/-! ## 4. Actual cutoff-one matching specialization -/

/-- The existing candidate-level observable matching defect is exactly the
sharp connected pushed-law remainder budget for its own structured
observable. -/
theorem physicalObservableMatchDefect_connected_eqv
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate)
    (M : SlabFaceBlockMap
      (G.candidateScalePair g hg candidate hcandidate)) :
    let S := G.candidateScalePair g hg candidate hcandidate
    let K := physicalKernel S rfl hcandidate
    observableMatchDefect G g hg candidate hcandidate
        (connectedRemainderObservable K M) ≈
      Q'.abs (centeredCylinderRemainder K M) := by
  dsimp only
  simpa only [observableMatchDefect, blockedObservableExpectation,
      coarseObservableExpectation, finiteKernelObservableMatchDefect] using
    (connectedObservableMatchDefect_eqv_abs_centeredCylinderRemainder
      (physicalKernel
        (G.candidateScalePair g hg candidate hcandidate)
        rfl hcandidate) M)

#print axioms remainderObservableExpectation
#print axioms blockedObservableExpectation_eqv_coarse_add_remainder
#print axioms blocked_sub_coarseObservableExpectation_eqv_remainder
#print axioms weightedCylinderObservable
#print axioms weightedCylinderRemainderExpectation_eqv
#print axioms connectedRemainderObservable
#print axioms connectedRemainderExpectation_eqv_centeredCylinderRemainder
#print axioms finiteKernelObservableMatchDefect
#print axioms connectedObservableMatchDefect_eqv_abs_centeredCylinderRemainder
#print axioms connectedRemainderObservable_abs_le_one
#print axioms remainderObservableExpectation_abs_le_remainderL1
#print axioms centeredCylinderRemainder_abs_le_remainderL1
#print axioms physicalObservableMatchDefect_connected_eqv

end YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
