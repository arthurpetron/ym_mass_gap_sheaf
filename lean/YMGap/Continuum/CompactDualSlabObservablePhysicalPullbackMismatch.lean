/-
# Kernel-row mismatch mass controls the physical observable pullback

The source-row Fubini formula identifies the signed cylinder discrepancy

  K(x,B) - 1_A(x)

for a fine source event `A` and coarse target event `B`.  This module turns
that signed quantity into a literal nonnegative geometric statistic.  If the
source lies in `A`, mismatch means that the kernel row exits `B`; otherwise it
means that the row enters `B`.  Row normalization proves exactly

  |K(x,B) - 1_A(x)| = K(x, mismatch(A,B)).

Finite triangle and Tonelli estimates then bound each source-averaged moment
remainder, and the connected root/target/joint pullback combination, by the
corresponding averaged mismatch masses.

No mismatch estimate for the actual recoupling kernel is asserted here.  The
new nonnegative cost is the geometric producer still requiring a uniform
refining-scale bound.

Constructive contract: finite exact-rational sums, row normalization, and
kernel nonnegativity only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackFubini

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackFubini
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail => by
      change
        Q'.abs (value head + listQSum value tail) ≤
          Q'.abs (value head) +
            listQSum (fun item => Q'.abs (value item)) tail
      exact Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add_left _ _ _
          (abs_listQSum_le_sum_abs_local value tail))

private theorem sub_one_eqv_neg_of_add_eqv_one
    (left right : Q') (htotal : left + right ≈ 1) :
    left - 1 ≈ -right := by
  refine Q'.eqv_trans _ (left + (-(left + right))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm htotal))
  refine Q'.eqv_trans _ (left + ((-left) + (-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_add_eqv left right)
  refine Q'.eqv_trans _ ((left + (-left)) + (-right)) _ ?_ ?_
  · exact Q'.eqv_symm (Q'.add_assoc_eqv left (-left) (-right))
  refine Q'.eqv_trans _ (0 + (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-right)
      (Q'.add_neg_self_eqv left)
  exact Q'.eqv_of_eq (Q'.zero_add' (-right))

private theorem abs_mul_le_of_right_unit_interval
    (value probability : Q')
    (hprobabilityNonnegative : (0 : Q') ≤ probability)
    (hprobabilityLeOne : probability ≤ (1 : Q')) :
    Q'.abs (value * probability) ≤ Q'.abs value := by
  refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le value probability) ?_
  refine Q'.le_trans' _
    (Q'.abs value * probability) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (Q'.abs value) _ _
        (Q'.eqv_of_eq
          (ExpNeg.abs_of_nonneg hprobabilityNonnegative)))
  refine Q'.le_trans' _ (Q'.abs value * 1) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      hprobabilityLeOne (Q'.abs_nonneg value)
  exact Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs value))

/-! ## 1. Literal row-mismatch mass -/

/-- For a fixed source, target mismatch means leaving the selected coarse
cylinder when the fine event is true, or entering it when the fine event is
false. -/
def cylinderPullbackMismatchEvent
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source target : EdgeLabelling) : Bool :=
  if fineEvent source then !(coarseEvent target) else coarseEvent target

/-- Nonnegative mass of the mismatch targets in one physical-kernel row. -/
def kernelRowCylinderMismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling) : Q' :=
  finiteEventMass (K.kernel source) S.coarse.physicalLabellings
    (cylinderPullbackMismatchEvent fineEvent coarseEvent source)

/-- Fine-law average of the literal row-mismatch mass. -/
def averagedCylinderPullbackMismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fun source =>
      S.fine.normalizedMass source *
        kernelRowCylinderMismatchMass K
          fineEvent coarseEvent source)
    S.fine.physicalLabellings

/-- Signed mismatch mass, oriented like `K(x,B) - 1_A(x)`. -/
def signedKernelRowCylinderMismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling) : Q' :=
  if fineEvent source then
    -(kernelRowCylinderMass K (fun target => !(coarseEvent target)) source)
  else
    kernelRowCylinderMass K coarseEvent source

theorem kernelRowCylinderMass_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    (0 : Q') ≤ kernelRowCylinderMass K coarseEvent source := by
  unfold kernelRowCylinderMass
  exact finiteEventMass_nonnegative
    (K.kernel source) S.coarse.physicalLabellings coarseEvent
    (fun target htarget => K.nonnegative source target hsource htarget)

theorem kernelRowCylinderMismatchMass_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    (0 : Q') ≤
      kernelRowCylinderMismatchMass K fineEvent coarseEvent source := by
  unfold kernelRowCylinderMismatchMass
  exact finiteEventMass_nonnegative
    (K.kernel source) S.coarse.physicalLabellings
    (cylinderPullbackMismatchEvent fineEvent coarseEvent source)
    (fun target htarget => K.nonnegative source target hsource htarget)

/-- An event and its Boolean complement partition every normalized kernel
row. -/
theorem kernelRowCylinderMass_add_complement_eqv_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    kernelRowCylinderMass K coarseEvent source +
        kernelRowCylinderMass K
          (fun target => !(coarseEvent target)) source ≈ 1 := by
  unfold kernelRowCylinderMass finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (if coarseEvent target then K.kernel source target else 0) +
          (if !(coarseEvent target) then K.kernel source target else 0))
      S.coarse.physicalLabellings) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_add
        (fun target =>
          if coarseEvent target then K.kernel source target else 0)
        (fun target =>
          if !(coarseEvent target) then K.kernel source target else 0)
        S.coarse.physicalLabellings)
  refine Q'.eqv_trans _
    (listQSum (K.kernel source) S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    cases hevent : coarseEvent target
    · simp only [Bool.not_false, Bool.false_eq_true, if_false, if_true]
      exact Q'.eqv_of_eq (Q'.zero_add' (K.kernel source target))
    · simp only [Bool.not_true, if_true]
      exact Q'.eqv_of_eq (Q'.add_zero' (K.kernel source target))
  exact K.row_normalized source hsource

/-- The signed Fubini integrand is exactly the signed literal mismatch mass. -/
theorem sourceCylinderPullbackDiscrepancy_eqv_signedMismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    sourceCylinderPullbackDiscrepancy K
        fineEvent coarseEvent source ≈
      signedKernelRowCylinderMismatchMass K
        fineEvent coarseEvent source := by
  cases hevent : fineEvent source
  · unfold sourceCylinderPullbackDiscrepancy booleanEventIndicator
      signedKernelRowCylinderMismatchMass
    simp only [hevent, Bool.false_eq_true, if_false]
    exact Q'.eqv_of_eq
      (Q'.sub_zero' (kernelRowCylinderMass K coarseEvent source))
  · unfold sourceCylinderPullbackDiscrepancy booleanEventIndicator
      signedKernelRowCylinderMismatchMass
    simp only [hevent, if_true]
    exact sub_one_eqv_neg_of_add_eqv_one _ _
      (kernelRowCylinderMass_add_complement_eqv_one
        K coarseEvent source hsource)

/-- The absolute row discrepancy is exactly the mass of targets on which the
fine and coarse cylinder values disagree. -/
theorem abs_sourceCylinderPullbackDiscrepancy_eqv_mismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool)
    (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    Q'.abs
        (sourceCylinderPullbackDiscrepancy K
          fineEvent coarseEvent source) ≈
      kernelRowCylinderMismatchMass K
        fineEvent coarseEvent source := by
  refine Q'.eqv_trans _
    (Q'.abs
      (signedKernelRowCylinderMismatchMass K
        fineEvent coarseEvent source)) _
    (Q'.abs_eqv_congr
      (sourceCylinderPullbackDiscrepancy_eqv_signedMismatchMass
        K fineEvent coarseEvent source hsource)) ?_
  cases hevent : fineEvent source
  · unfold signedKernelRowCylinderMismatchMass
      kernelRowCylinderMismatchMass cylinderPullbackMismatchEvent
      kernelRowCylinderMass
    simp only [hevent, Bool.false_eq_true, if_false]
    exact Q'.eqv_of_eq
      (ExpNeg.abs_of_nonneg
        (kernelRowCylinderMass_nonnegative
          K coarseEvent source hsource))
  · unfold signedKernelRowCylinderMismatchMass
      kernelRowCylinderMismatchMass cylinderPullbackMismatchEvent
      kernelRowCylinderMass
    simp only [hevent, if_true]
    refine Q'.eqv_trans _
      (Q'.abs
        (finiteEventMass (K.kernel source)
          S.coarse.physicalLabellings
          (fun target => !(coarseEvent target)))) _
      (Q'.abs_neg' _)
      (Q'.eqv_of_eq
        (ExpNeg.abs_of_nonneg
          (kernelRowCylinderMass_nonnegative K
            (fun target => !(coarseEvent target)) source hsource)))

/-- The absolute signed cylinder remainder is controlled by the fine-law
average of literal kernel-row mismatch mass. -/
theorem abs_averagedCylinderPullbackRemainder_le_mismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineEvent coarseEvent : EdgeLabelling → Bool) :
    Q'.abs
        (averagedCylinderPullbackRemainder K fineEvent coarseEvent) ≤
      averagedCylinderPullbackMismatchMass K fineEvent coarseEvent := by
  unfold averagedCylinderPullbackRemainder
    averagedCylinderPullbackMismatchMass
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local
      (fun source =>
        S.fine.normalizedMass source *
          sourceCylinderPullbackDiscrepancy K
            fineEvent coarseEvent source)
      S.fine.physicalLabellings) ?_
  apply listQSum_mono_local
  intro source hsource
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le
      (S.fine.normalizedMass source)
      (sourceCylinderPullbackDiscrepancy K
        fineEvent coarseEvent source)) ?_
  exact Q'.le_of_eqv
    (mul_eqv_both_local
      (Q'.eqv_of_eq
        (ExpNeg.abs_of_nonneg
          (S.fine.normalizedMass_nonnegative source)))
      (abs_sourceCylinderPullbackDiscrepancy_eqv_mismatchMass
        K fineEvent coarseEvent source hsource))

/-! ## 2. Face mismatch costs and the connected pullback -/

def faceSourcePullbackMismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineFaceId coarseFaceId : Nat) : Q' :=
  averagedCylinderPullbackMismatchMass K
    (slabPhysicalFacePositiveB fineFaceId)
    (slabPhysicalFacePositiveB coarseFaceId)

def facePairSourcePullbackMismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) : Q' :=
  averagedCylinderPullbackMismatchMass K
    (slabPhysicalFacePairPositiveB fineRoot fineTarget)
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

/-- Total root/target/joint geometric mismatch cost consumed by one Boolean
face covariance. -/
def observableSourcePullbackMismatchCost
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  facePairSourcePullbackMismatchMass K
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget +
    (faceSourcePullbackMismatchMass K M.fineRoot M.coarseRoot +
      faceSourcePullbackMismatchMass K M.fineTarget M.coarseTarget)

theorem faceSourcePullbackRemainder_abs_le_mismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineFaceId coarseFaceId : Nat) :
    Q'.abs (faceSourcePullbackRemainder K fineFaceId coarseFaceId) ≤
      faceSourcePullbackMismatchMass K fineFaceId coarseFaceId := by
  unfold faceSourcePullbackRemainder faceSourcePullbackMismatchMass
  exact abs_averagedCylinderPullbackRemainder_le_mismatchMass K
    (slabPhysicalFacePositiveB fineFaceId)
    (slabPhysicalFacePositiveB coarseFaceId)

theorem facePairSourcePullbackRemainder_abs_le_mismatchMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) :
    Q'.abs
        (facePairSourcePullbackRemainder K
          fineRoot fineTarget coarseRoot coarseTarget) ≤
      facePairSourcePullbackMismatchMass K
        fineRoot fineTarget coarseRoot coarseTarget := by
  unfold facePairSourcePullbackRemainder
    facePairSourcePullbackMismatchMass
  exact abs_averagedCylinderPullbackRemainder_le_mismatchMass K
    (slabPhysicalFacePairPositiveB fineRoot fineTarget)
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

private theorem fineFaceMoment_nonnegative_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    (0 : Q') ≤ fineFaceMoment K faceId := by
  unfold fineFaceMoment PhysicalKernel.fineCylinderMass
  exact finiteEventMass_nonnegative
    S.fine.normalizedMass S.fine.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun source _ => S.fine.normalizedMass_nonnegative source)

private theorem fineFaceMoment_le_one_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    fineFaceMoment K faceId ≤ (1 : Q') := by
  unfold fineFaceMoment PhysicalKernel.fineCylinderMass
  exact finiteEventMass_le_one
    S.fine.normalizedMass S.fine.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun source _ => S.fine.normalizedMass_nonnegative source)
    S.fine.normalizedMass_total

private theorem blockedFaceMoment_nonnegative_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    (0 : Q') ≤ blockedFaceMoment K faceId := by
  unfold blockedFaceMoment PhysicalKernel.blockedCylinderMass
  exact finiteEventMass_nonnegative
    K.blockedMass S.coarse.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun _ htarget => K.blockedMass_nonnegative htarget)

private theorem blockedFaceMoment_le_one_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    blockedFaceMoment K faceId ≤ (1 : Q') := by
  unfold blockedFaceMoment PhysicalKernel.blockedCylinderMass
  exact finiteEventMass_le_one
    K.blockedMass S.coarse.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun _ htarget => K.blockedMass_nonnegative htarget)
    K.blockedMass_total

/-- The absolute connected stochastic pullback remainder is controlled by a
literal nonnegative root/target/joint row-mismatch cost. -/
theorem centeredObservablePullbackSourceRemainder_abs_le_mismatchCost
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    Q'.abs (centeredObservablePullbackSourceRemainder K M) ≤
      observableSourcePullbackMismatchCost K M := by
  let joint := facePairSourcePullbackRemainder K
    M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget
  let root := faceSourcePullbackRemainder K M.fineRoot M.coarseRoot
  let target := faceSourcePullbackRemainder K
    M.fineTarget M.coarseTarget
  let blockedTarget := blockedFaceMoment K M.coarseTarget
  let fineRoot := fineFaceMoment K M.fineRoot
  have hjoint : Q'.abs (-joint) ≤
      facePairSourcePullbackMismatchMass K
        M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' joint))
      (facePairSourcePullbackRemainder_abs_le_mismatchMass K
        M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget)
  have hroot : Q'.abs (root * blockedTarget) ≤
      faceSourcePullbackMismatchMass K M.fineRoot M.coarseRoot :=
    Q'.le_trans' _ _ _
      (abs_mul_le_of_right_unit_interval root blockedTarget
        (blockedFaceMoment_nonnegative_local K M.coarseTarget)
        (blockedFaceMoment_le_one_local K M.coarseTarget))
      (faceSourcePullbackRemainder_abs_le_mismatchMass K
        M.fineRoot M.coarseRoot)
  have htarget : Q'.abs (fineRoot * target) ≤
      faceSourcePullbackMismatchMass K M.fineTarget M.coarseTarget := by
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le fineRoot target) ?_
    refine Q'.le_trans' _ (fineRoot * Q'.abs target) _ ?_ ?_
    · exact Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _ (Q'.abs target)
          (Q'.eqv_of_eq
            (ExpNeg.abs_of_nonneg
              (fineFaceMoment_nonnegative_local K M.fineRoot))))
    refine Q'.le_trans' _ ((1 : Q') * Q'.abs target) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (fineFaceMoment_le_one_local K M.fineRoot)
        (Q'.abs_nonneg target)
    refine Q'.le_trans' _ (Q'.abs target) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs target))
    exact faceSourcePullbackRemainder_abs_le_mismatchMass K
      M.fineTarget M.coarseTarget
  unfold centeredObservablePullbackSourceRemainder
    observableSourcePullbackMismatchCost
  refine Q'.le_trans' _
    (Q'.abs (-joint) +
      Q'.abs (root * blockedTarget + fineRoot * target)) _ ?_ ?_
  · exact Q'.abs_add_le' (-joint)
      (root * blockedTarget + fineRoot * target)
  refine Q'.le_trans' _
    (Q'.abs (-joint) +
      (Q'.abs (root * blockedTarget) + Q'.abs (fineRoot * target))) _ ?_ ?_
  · exact Q'.add_le_add_left _ _ _
      (Q'.abs_add_le' (root * blockedTarget) (fineRoot * target))
  exact Q'.add_le_add hjoint (Q'.add_le_add hroot htarget)

#print axioms cylinderPullbackMismatchEvent
#print axioms kernelRowCylinderMismatchMass
#print axioms averagedCylinderPullbackMismatchMass
#print axioms signedKernelRowCylinderMismatchMass
#print axioms kernelRowCylinderMass_nonnegative
#print axioms kernelRowCylinderMismatchMass_nonnegative
#print axioms kernelRowCylinderMass_add_complement_eqv_one
#print axioms sourceCylinderPullbackDiscrepancy_eqv_signedMismatchMass
#print axioms abs_sourceCylinderPullbackDiscrepancy_eqv_mismatchMass
#print axioms abs_averagedCylinderPullbackRemainder_le_mismatchMass
#print axioms faceSourcePullbackMismatchMass
#print axioms facePairSourcePullbackMismatchMass
#print axioms observableSourcePullbackMismatchCost
#print axioms faceSourcePullbackRemainder_abs_le_mismatchMass
#print axioms facePairSourcePullbackRemainder_abs_le_mismatchMass
#print axioms centeredObservablePullbackSourceRemainder_abs_le_mismatchCost

end YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackMismatch
