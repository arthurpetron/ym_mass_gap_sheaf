/-
# Source-row Fubini formula for the physical observable pullback

The centered physical blocking interface isolates the stochastic discrepancy
between a fine Boolean cylinder and the pullback of its selected coarse
cylinder.  The signed root, target, and joint moment differences are exact,
but their definitions as differences of pushed and fine masses do not yet
display the source-local kernel quantity that a geometric estimate must bound.

This module applies finite exact-rational Fubini to expose that quantity.  For
each fine source state, the kernel row assigns a conditional mass to the coarse
cylinder.  Subtracting the zero--one fine-cylinder indicator gives a rowwise
pullback discrepancy, and averaging it against the normalized fine physical
law gives exactly the signed moment remainder.  The connected pullback
remainder is consequently an exact combination of three such source averages.

No pointwise locality, smallness, or refining-scale decay is asserted here.

Constructive contract: finite exact-rational sums and the existing physical
kernel only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackFubini

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum (fun item => left item - right item) items ≈
      listQSum left items - listQSum right items := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl _) (listQSum_neg_local right items)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_sub_distribute_local (a b c : Q') :
    a * b - a * c ≈ a * (b - c) := by
  refine Q'.eqv_trans _ (a * b + a * (-c)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm (Q'.mul_neg_eqv a c))
  exact Q'.eqv_symm (Q'.mul_add_eqv a b (-c))

/-! ## 1. Generic rowwise cylinder discrepancy -/

/-- Exact zero--one rational indicator of a Boolean event. -/
def booleanEventIndicator {A : Type} (event : A → Bool) (state : A) : Q' :=
  if event state then 1 else 0

/-- Conditional mass that one physical-kernel row assigns to a selected
coarse Boolean cylinder. -/
def kernelRowCylinderMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling) : Q' :=
  finiteEventMass (K.kernel source)
    S.coarse.physicalLabellings coarseEvent

/-- The source-local failure of a stochastic row to transport the chosen fine
Boolean cylinder to the chosen coarse cylinder. -/
def sourceCylinderPullbackDiscrepancy
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling) : Q' :=
  kernelRowCylinderMass K coarseEvent source -
    booleanEventIndicator fineEvent source

/-- Fine-law average of the rowwise cylinder-pullback discrepancy. -/
def averagedCylinderPullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fun source =>
      S.fine.normalizedMass source *
        sourceCylinderPullbackDiscrepancy K
          fineEvent coarseEvent source)
    S.fine.physicalLabellings

/-- Finite Fubini rewrites pushed coarse-cylinder mass as the fine-law average
of the corresponding conditional kernel-row mass. -/
theorem blockedCylinderMass_eqv_sourceRowCylinderAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (coarseEvent : EdgeLabelling → Bool) :
    PhysicalKernel.blockedCylinderMass K coarseEvent ≈
      listQSum
        (fun source =>
          S.fine.normalizedMass source *
            kernelRowCylinderMass K coarseEvent source)
        S.fine.physicalLabellings := by
  unfold PhysicalKernel.blockedCylinderMass
    SlabScalePair.FiniteSlabKernel.blockedMass
    kernelRowCylinderMass finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            if coarseEvent target then
              S.fine.normalizedMass source * K.kernel source target
            else 0)
          S.fine.physicalLabellings)
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    cases hevent : coarseEvent target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm
        (listQSum_zero S.fine.physicalLabellings)
    · simp only [if_true]
      exact Q'.eqv_refl _
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            if coarseEvent target then
              S.fine.normalizedMass source * K.kernel source target
            else 0)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        if coarseEvent target then
          S.fine.normalizedMass source * K.kernel source target
        else 0)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  · apply listQSum_congr_on
    intro source _
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          S.fine.normalizedMass source *
            (if coarseEvent target then K.kernel source target else 0))
        S.coarse.physicalLabellings) _ ?_ ?_
    · apply listQSum_congr_on
      intro target _
      cases hevent : coarseEvent target
      · simp only [Bool.false_eq_true, if_false]
        exact Q'.eqv_symm
          (Q'.mul_zero_eqv (S.fine.normalizedMass source))
      · simp only [if_true]
        exact Q'.eqv_refl _
    exact listQSum_mul_left
      (S.fine.normalizedMass source)
      (fun target =>
        if coarseEvent target then K.kernel source target else 0)
      S.coarse.physicalLabellings

/-- Fine Boolean-cylinder mass is the fine-law average of its zero--one
indicator. -/
theorem fineCylinderMass_eqv_sourceIndicatorAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent : EdgeLabelling → Bool) :
    PhysicalKernel.fineCylinderMass K fineEvent ≈
      listQSum
        (fun source =>
          S.fine.normalizedMass source *
            booleanEventIndicator fineEvent source)
        S.fine.physicalLabellings := by
  unfold PhysicalKernel.fineCylinderMass finiteEventMass
  apply listQSum_congr_on
  intro source _
  unfold booleanEventIndicator
  cases hevent : fineEvent source
  · simp only [Bool.false_eq_true, if_false]
    exact Q'.eqv_symm
      (Q'.mul_zero_eqv (S.fine.normalizedMass source))
  · simp only [if_true]
    exact Q'.eqv_symm
      (Q'.mul_one_eqv (S.fine.normalizedMass source))

/-- Exact generic source-row formula for the signed pullback of a Boolean
cylinder. -/
theorem blocked_sub_fineCylinderMass_eqv_averagedPullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    PhysicalKernel.blockedCylinderMass K coarseEvent -
        PhysicalKernel.fineCylinderMass K fineEvent ≈
      averagedCylinderPullbackRemainder K fineEvent coarseEvent := by
  let pushedTerm := fun source =>
    S.fine.normalizedMass source *
      kernelRowCylinderMass K coarseEvent source
  let indicatorTerm := fun source =>
    S.fine.normalizedMass source *
      booleanEventIndicator fineEvent source
  refine Q'.eqv_trans _
    (listQSum pushedTerm S.fine.physicalLabellings -
      listQSum indicatorTerm S.fine.physicalLabellings) _ ?_ ?_
  · exact sub_eqv_both_local
      (blockedCylinderMass_eqv_sourceRowCylinderAverage K coarseEvent)
      (fineCylinderMass_eqv_sourceIndicatorAverage K fineEvent)
  refine Q'.eqv_trans _
    (listQSum
      (fun source => pushedTerm source - indicatorTerm source)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_sub_local pushedTerm indicatorTerm
        S.fine.physicalLabellings)
  unfold averagedCylinderPullbackRemainder
    sourceCylinderPullbackDiscrepancy pushedTerm indicatorTerm
  apply listQSum_congr_on
  intro source _
  exact mul_sub_distribute_local
    (S.fine.normalizedMass source)
    (kernelRowCylinderMass K coarseEvent source)
    (booleanEventIndicator fineEvent source)

/-! ## 2. Literal face specializations and connected combination -/

/-- Source-averaged row discrepancy for one selected fine/coarse face pair. -/
def faceSourcePullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineFaceId coarseFaceId : Nat) : Q' :=
  averagedCylinderPullbackRemainder K
    (slabPhysicalFacePositiveB fineFaceId)
    (slabPhysicalFacePositiveB coarseFaceId)

/-- Source-averaged row discrepancy for the joint selected face event. -/
def facePairSourcePullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) : Q' :=
  averagedCylinderPullbackRemainder K
    (slabPhysicalFacePairPositiveB fineRoot fineTarget)
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

/-- The connected pullback remainder written entirely in terms of its three
source-averaged kernel-row discrepancies. -/
def centeredObservablePullbackSourceRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  -(facePairSourcePullbackRemainder K
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget) +
    (faceSourcePullbackRemainder K M.fineRoot M.coarseRoot *
        blockedFaceMoment K M.coarseTarget +
      fineFaceMoment K M.fineRoot *
        faceSourcePullbackRemainder K M.fineTarget M.coarseTarget)

theorem facePullbackRemainder_eqv_sourceAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineFaceId coarseFaceId : Nat) :
    facePullbackRemainder K fineFaceId coarseFaceId ≈
      faceSourcePullbackRemainder K fineFaceId coarseFaceId := by
  unfold facePullbackRemainder blockedFaceMoment fineFaceMoment
    faceSourcePullbackRemainder
  exact blocked_sub_fineCylinderMass_eqv_averagedPullbackRemainder K
    (slabPhysicalFacePositiveB fineFaceId)
    (slabPhysicalFacePositiveB coarseFaceId)

theorem facePairPullbackRemainder_eqv_sourceAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) :
    facePairPullbackRemainder K
        fineRoot fineTarget coarseRoot coarseTarget ≈
      facePairSourcePullbackRemainder K
        fineRoot fineTarget coarseRoot coarseTarget := by
  unfold facePairPullbackRemainder blockedFacePairMoment
    fineFacePairMoment facePairSourcePullbackRemainder
  exact blocked_sub_fineCylinderMass_eqv_averagedPullbackRemainder K
    (slabPhysicalFacePairPositiveB fineRoot fineTarget)
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

/-- Exact source-row representation of the full connected stochastic
observable-pullback remainder. -/
theorem centeredObservablePullbackRemainder_eqv_sourceAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    centeredObservablePullbackRemainder K M ≈
      centeredObservablePullbackSourceRemainder K M := by
  unfold centeredObservablePullbackRemainder
    centeredObservablePullbackSourceRemainder
  exact Q'.add_eqv_congr'
    (Q'.neg_eqv_congr _ _
      (facePairPullbackRemainder_eqv_sourceAverage K
        M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget))
    (Q'.add_eqv_congr'
      (mul_eqv_both_local
        (facePullbackRemainder_eqv_sourceAverage K
          M.fineRoot M.coarseRoot)
        (Q'.eqv_refl _))
      (mul_eqv_both_local
        (Q'.eqv_refl _)
        (facePullbackRemainder_eqv_sourceAverage K
          M.fineTarget M.coarseTarget)))

/-- The centered stochastic pullback defect is exactly the absolute value of
the connected source-row average. -/
theorem centeredObservablePullbackDefect_eqv_abs_sourceAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    centeredObservablePullbackDefect K M ≈
      Q'.abs (centeredObservablePullbackSourceRemainder K M) := by
  exact Q'.eqv_trans _
    (Q'.abs (centeredObservablePullbackRemainder K M)) _
    (centeredObservablePullbackDefect_eqv_abs_centeredPullbackRemainder K M)
    (Q'.abs_eqv_congr
      (centeredObservablePullbackRemainder_eqv_sourceAverage K M))

#print axioms booleanEventIndicator
#print axioms kernelRowCylinderMass
#print axioms sourceCylinderPullbackDiscrepancy
#print axioms averagedCylinderPullbackRemainder
#print axioms blockedCylinderMass_eqv_sourceRowCylinderAverage
#print axioms fineCylinderMass_eqv_sourceIndicatorAverage
#print axioms blocked_sub_fineCylinderMass_eqv_averagedPullbackRemainder
#print axioms faceSourcePullbackRemainder
#print axioms facePairSourcePullbackRemainder
#print axioms centeredObservablePullbackSourceRemainder
#print axioms facePullbackRemainder_eqv_sourceAverage
#print axioms facePairPullbackRemainder_eqv_sourceAverage
#print axioms centeredObservablePullbackRemainder_eqv_sourceAverage
#print axioms centeredObservablePullbackDefect_eqv_abs_sourceAverage

end YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackFubini
