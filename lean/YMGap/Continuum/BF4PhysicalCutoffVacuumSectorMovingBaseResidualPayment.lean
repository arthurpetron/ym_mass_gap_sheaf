/-
# Generic moving-base scalar payment with a component-merger reserve

The moving-base mass decomposition isolates the exact finite scalar burden
that a local flow argument must pay.  This file uses the literal later vacuum
sector size, an explicitly supplied positive coercivity floor, the corrected-
slab increment, the component-merger mass, and the already constructed later
vacuum-sector edge floor.

The total payment demand splits exactly into increment and merger demands.  A
division-free reserve certificate compiles to the total payment, which in turn
pays the scaled new-block mass.  A successful no-merger check reduces the same
obligation to its increment-only part.  The equal-cutoff residual certificate
is explicitly inhabited for every positive coercivity floor.

This is the generic scalar layer only.  No generic moving-base path flow,
old-block coercivity transport, nontrivial local payment, cofinal schedule,
thermodynamic/continuum construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal finite size and the three scalar demands -/

/-- The actual number of states in the later canonical vacuum component. -/
def centralPhysicalFiniteMovingBaseStateCount
    (w : Q') (hw : (0 : Q') ≤ w)
    (later half : Nat) : Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw later half).length

def centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coercivityFloor : Q') : Q' :=
  coercivityFloor *
    (Q'.ofNat
        (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
      (Q'.ofNat 2 *
        (slabParametricKCutoffIncrement
            w base later (centralExtent half) +
          centralPhysicalFiniteNewComponentMergerMass
            w hw base later half)))

def centralPhysicalFiniteMovingBaseIncrementPaymentDemand
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coercivityFloor : Q') : Q' :=
  coercivityFloor *
    (Q'.ofNat
        (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
      (Q'.ofNat 2 *
        slabParametricKCutoffIncrement
          w base later (centralExtent half)))

def centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coercivityFloor : Q') : Q' :=
  coercivityFloor *
    (Q'.ofNat
        (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
      (Q'.ofNat 2 *
        centralPhysicalFiniteNewComponentMergerMass
          w hw base later half))

def centralPhysicalFiniteMovingBaseEdgePaymentBudget
    (w : Q') (hw : (0 : Q') ≤ w)
    (later half : Nat) : Q' :=
  HalfPow.half *
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw later half

theorem centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand_eqv_increment_add_merger
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coercivityFloor : Q') :
    centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
        w hw base later half coercivityFloor ≈
      centralPhysicalFiniteMovingBaseIncrementPaymentDemand
          w hw base later half coercivityFloor +
        centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
          w hw base later half coercivityFloor := by
  let size := Q'.ofNat
    (centralPhysicalFiniteMovingBaseStateCount w hw later half)
  let increment := slabParametricKCutoffIncrement
    w base later (centralExtent half)
  let merger := centralPhysicalFiniteNewComponentMergerMass
    w hw base later half
  have htwo :
      Q'.ofNat 2 * (increment + merger) ≈
        Q'.ofNat 2 * increment + Q'.ofNat 2 * merger :=
    Q'.mul_add_eqv _ _ _
  have hsizeCongr :
      size * (Q'.ofNat 2 * (increment + merger)) ≈
        size * (Q'.ofNat 2 * increment + Q'.ofNat 2 * merger) :=
    Q'.mul_eqv_congr_left size _ _ htwo
  have hsizeDist :
      size * (Q'.ofNat 2 * increment + Q'.ofNat 2 * merger) ≈
        size * (Q'.ofNat 2 * increment) +
          size * (Q'.ofNat 2 * merger) :=
    Q'.mul_add_eqv _ _ _
  have hsize := Q'.eqv_trans _ _ _ hsizeCongr hsizeDist
  have hfloorCongr :
      coercivityFloor *
          (size * (Q'.ofNat 2 * (increment + merger))) ≈
        coercivityFloor *
          (size * (Q'.ofNat 2 * increment) +
            size * (Q'.ofNat 2 * merger)) :=
    Q'.mul_eqv_congr_left coercivityFloor _ _ hsize
  have hfloorDist :
      coercivityFloor *
          (size * (Q'.ofNat 2 * increment) +
            size * (Q'.ofNat 2 * merger)) ≈
        coercivityFloor * (size * (Q'.ofNat 2 * increment)) +
          coercivityFloor * (size * (Q'.ofNat 2 * merger)) :=
    Q'.mul_add_eqv _ _ _
  unfold centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
    centralPhysicalFiniteMovingBaseIncrementPaymentDemand
    centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
  exact Q'.eqv_trans _ _ _ hfloorCongr hfloorDist

/-! ## 2. Positivity and the division-free residual budget -/

theorem centralPhysicalFiniteMovingBaseIncrementPaymentDemand_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) {coercivityFloor : Q'}
    (hcoercivity : (0 : Q') ≤ coercivityFloor) :
    (0 : Q') ≤ centralPhysicalFiniteMovingBaseIncrementPaymentDemand
      w hw base later half coercivityFloor := by
  unfold centralPhysicalFiniteMovingBaseIncrementPaymentDemand
  apply Q'.mul_nonneg _ _ hcoercivity
  apply Q'.mul_nonneg
  · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
  · apply Q'.mul_nonneg
    · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
    · exact slabParametricKCutoffIncrement_nonnegative
        hw base later (centralExtent half)

theorem centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) {coercivityFloor : Q'}
    (hcoercivity : (0 : Q') ≤ coercivityFloor) :
    (0 : Q') ≤ centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
      w hw base later half coercivityFloor := by
  unfold centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
  apply Q'.mul_nonneg _ _ hcoercivity
  apply Q'.mul_nonneg
  · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
  · apply Q'.mul_nonneg
    · exact YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _
    · exact centralPhysicalFiniteNewComponentMergerMass_nonnegative
        w hw base later half

theorem centralPhysicalFiniteMovingBaseEdgePaymentBudget_pos
    (w : Q') (hw : (0 : Q') ≤ w)
    (later half : Nat) :
    (0 : Q') < centralPhysicalFiniteMovingBaseEdgePaymentBudget
      w hw later half := by
  unfold centralPhysicalFiniteMovingBaseEdgePaymentBudget
  exact Q'.mul_pos (by decide)
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      w hw later half)

structure CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  hcutoff : base ≤ later
  coercivityFloor : Q'
  coercivityFloor_pos : (0 : Q') < coercivityFloor
  reserve : Q'
  increment_plus_reserve_le_budget :
    centralPhysicalFiniteMovingBaseIncrementPaymentDemand
        w hw base later half coercivityFloor + reserve ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half
  merger_demand_le_reserve :
    centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
        w hw base later half coercivityFloor ≤ reserve

namespace CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt

theorem reserve_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt
      w hw base later half) :
    (0 : Q') ≤ certificate.reserve :=
  Q'.le_trans' _ _ _
    (centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand_nonnegative
      base later half (Q'.le_of_lt certificate.coercivityFloor_pos))
    certificate.merger_demand_le_reserve

theorem componentSplitPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt
      w hw base later half) :
    centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
        w hw base later half certificate.coercivityFloor ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half := by
  have hreplace :
      centralPhysicalFiniteMovingBaseIncrementPaymentDemand
          w hw base later half certificate.coercivityFloor +
          centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
            w hw base later half certificate.coercivityFloor ≤
        centralPhysicalFiniteMovingBaseIncrementPaymentDemand
            w hw base later half certificate.coercivityFloor +
          certificate.reserve :=
    Q'.add_le_add_left _ _ _ certificate.merger_demand_le_reserve
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand_eqv_increment_add_merger
        w hw base later half certificate.coercivityFloor))
    (Q'.le_trans' _ _ _ hreplace
      certificate.increment_plus_reserve_le_budget)

end CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt

/-! ## 3. The component split pays scaled new-block mass -/

theorem centralPhysicalFiniteMovingBaseNewMassPayment_of_componentSplitPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} {coercivityFloor : Q'}
    (hcutoff : base ≤ later)
    (hcoercivity : (0 : Q') ≤ coercivityFloor)
    (hpayment :
      centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
          w hw base later half coercivityFloor ≤
        centralPhysicalFiniteMovingBaseEdgePaymentBudget
          w hw later half) :
    coercivityFloor *
        (Q'.ofNat
            (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
          (Q'.ofNat 2 *
            centralPhysicalFiniteVacuumSectorNewMass
              w hw base later half)) ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half := by
  have hnew :=
    centralPhysicalFiniteVacuumSectorNewMass_le_increment_add_merger
      (w := w) (hw := hw) (half := half) hcutoff
  have htwo := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hnew
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat 2)
  have hsize := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat
      (centralPhysicalFiniteMovingBaseStateCount w hw later half))
    htwo
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    coercivityFloor hsize hcoercivity
  exact Q'.le_trans' _ _ _ hscaled hpayment

theorem CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt.newMassPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat}
    (certificate : CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt
      w hw base later half) :
    certificate.coercivityFloor *
        (Q'.ofNat
            (centralPhysicalFiniteMovingBaseStateCount w hw later half) *
          (Q'.ofNat 2 *
            centralPhysicalFiniteVacuumSectorNewMass
              w hw base later half)) ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half :=
  centralPhysicalFiniteMovingBaseNewMassPayment_of_componentSplitPayment
    certificate.hcutoff (Q'.le_of_lt certificate.coercivityFloor_pos)
    certificate.componentSplitPayment

/-! ## 4. A successful no-merger check leaves increment-only payment -/

theorem centralPhysicalFiniteMovingBaseComponentSplitPayment_of_noMergerIncrementPayment
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} {coercivityFloor : Q'}
    (hcheck : centralPhysicalFiniteNoComponentMergerCheck
      w hw base later half = true)
    (hpayment :
      centralPhysicalFiniteMovingBaseIncrementPaymentDemand
          w hw base later half coercivityFloor ≤
        centralPhysicalFiniteMovingBaseEdgePaymentBudget
          w hw later half) :
    centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand
        w hw base later half coercivityFloor ≤
      centralPhysicalFiniteMovingBaseEdgePaymentBudget
        w hw later half := by
  let increment := slabParametricKCutoffIncrement
    w base later (centralExtent half)
  let merger := centralPhysicalFiniteNewComponentMergerMass
    w hw base later half
  have hzero : merger ≈ 0 :=
    centralPhysicalFiniteNewComponentMergerMass_eqv_zero_of_check hcheck
  have hadd : increment + merger ≈ increment :=
    Q'.eqv_trans _ (increment + 0) _
      (Q'.add_eqv_congr_left increment _ 0 hzero)
      (Q'.eqv_of_eq (Q'.add_zero' increment))
  have htwo := Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hadd
  have hsize := Q'.mul_eqv_congr_left
    (Q'.ofNat
      (centralPhysicalFiniteMovingBaseStateCount w hw later half))
    _ _ htwo
  have hscaled := Q'.mul_eqv_congr_left coercivityFloor _ _ hsize
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled) hpayment

/-! ## 5. Equal cutoffs inhabit the residual certificate -/

private theorem filter_not_true_empty_local
    {A : Type} (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = true) →
      items.filter (fun item => !(test item)) = []
  | [], _ => rfl
  | head :: tail, htrue => by
      have hhead := htrue head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → test item = true :=
        fun item hitem => htrue item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead, Bool.not_true,
        Bool.false_eq_true, if_false]
      exact filter_not_true_empty_local test tail htail

private theorem range_nodup_local :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨range_nodup_local count,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl count) (List.mem_range.mp hleft)

private theorem slabPhysicalFaceEdges_nodup_local (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact range_nodup_local _

theorem slabParametricKCutoffIncrement_self_eqv_zero
    (w : Q') (cutoff extent : Nat) :
    slabParametricKCutoffIncrement
      w cutoff cutoff extent ≈ 0 := by
  let faces := slabPhysicalFaceEdges extent
  let states := boundedEdgeLabellings cutoff faces
  have hfilter : states.filter (labelWithinB cutoff faces) = states := by
    dsimp only [states, faces]
    exact boundedEdgeLabellings_filter_cutoff
      (Nat.le_refl cutoff) _ (slabPhysicalFaceEdges_nodup_local extent)
  have hall : ∀ state, state ∈ states →
      labelWithinB cutoff faces state = true := by
    intro state hstate
    have hfiltered : state ∈ states.filter (labelWithinB cutoff faces) := by
      rw [hfilter]
      exact hstate
    exact (List.mem_filter.mp hfiltered).2
  have hempty :
      states.filter (fun state => !(labelWithinB cutoff faces state)) = [] :=
    filter_not_true_empty_local (labelWithinB cutoff faces) states hall
  unfold slabParametricKCutoffIncrement
  dsimp only [states, faces] at hempty ⊢
  rw [hempty]
  exact Q'.eqv_refl 0

private theorem centralPhysicalFiniteMovingBaseIncrementPaymentDemand_self_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coercivityFloor : Q') :
    centralPhysicalFiniteMovingBaseIncrementPaymentDemand
      w hw cutoff cutoff half coercivityFloor ≈ 0 := by
  have hinc := slabParametricKCutoffIncrement_self_eqv_zero
    w cutoff (centralExtent half)
  refine Q'.eqv_trans _
    (coercivityFloor *
      (Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) *
        (Q'.ofNat 2 * 0))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coercivityFloor _ _
      (Q'.mul_eqv_congr_left
        (Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half))
        _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ 0 hinc))
  exact Q'.eqv_trans _ (coercivityFloor *
      (Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) * 0)) _
    (Q'.mul_eqv_congr_left coercivityFloor _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv _)))
    (Q'.mul_zero_eqv coercivityFloor)

private theorem centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand_self_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coercivityFloor : Q') :
    centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand
      w hw cutoff cutoff half coercivityFloor ≈ 0 := by
  have hmerger := centralPhysicalFiniteNewComponentMergerMass_self_eqv_zero
    w hw cutoff half
  refine Q'.eqv_trans _
    (coercivityFloor *
      (Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) *
        (Q'.ofNat 2 * 0))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coercivityFloor _ _
      (Q'.mul_eqv_congr_left
        (Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half))
        _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ 0 hmerger))
  exact Q'.eqv_trans _ (coercivityFloor *
      (Q'.ofNat
          (centralPhysicalFiniteMovingBaseStateCount w hw cutoff half) * 0)) _
    (Q'.mul_eqv_congr_left coercivityFloor _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.mul_zero_eqv _)))
    (Q'.mul_zero_eqv coercivityFloor)

def centralPhysicalFiniteMovingBaseMergerResidualBudgetAt_self
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (coercivityFloor : Q')
    (hcoercivity : (0 : Q') < coercivityFloor) :
    CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt
      w hw cutoff cutoff half where
  hcutoff := Nat.le_refl cutoff
  coercivityFloor := coercivityFloor
  coercivityFloor_pos := hcoercivity
  reserve := 0
  increment_plus_reserve_le_budget := by
    have hzero :=
      centralPhysicalFiniteMovingBaseIncrementPaymentDemand_self_eqv_zero
        w hw cutoff half coercivityFloor
    have hleft :
        centralPhysicalFiniteMovingBaseIncrementPaymentDemand
            w hw cutoff cutoff half coercivityFloor + 0 ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ 0 0 hzero)
        (Q'.eqv_of_eq (Q'.zero_add' 0))
    exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hleft)
      (Q'.le_of_lt
        (centralPhysicalFiniteMovingBaseEdgePaymentBudget_pos
          w hw cutoff half))
  merger_demand_le_reserve :=
    Q'.le_of_eqv
      (centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand_self_eqv_zero
        w hw cutoff half coercivityFloor)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand_eqv_increment_add_merger
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseIncrementPaymentDemand_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseComponentMergerPaymentDemand_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseEdgePaymentBudget_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt.reserve_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt.componentSplitPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseNewMassPayment_of_componentSplitPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt.newMassPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseComponentSplitPayment_of_noMergerIncrementPayment
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.slabParametricKCutoffIncrement_self_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.centralPhysicalFiniteMovingBaseMergerResidualBudgetAt_self
