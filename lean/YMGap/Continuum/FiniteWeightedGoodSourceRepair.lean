/-
# Bounded-congestion weighted repair into a good finite subcarrier

A good-event density should not be postulated when it can be obtained by a
Peierls repair.  This module isolates the exact finite statement.  Every
source is repaired into a displayed good target.  If

```text
  lambda * sourceWeight(source) <= targetWeight(repair source)
```

and no target has more than `congestion + 1` repair preimages, then the good
target mass contains at least

```text
  lambda / (congestion + 1)
```

of the complete source mass.  Source and target weights may differ; this is
the weighted domination needed when a component peel changes physical spin
labels.  It is distinct from a same-physical-label recoupling channel.

Constructive contract: exact finite rational transport and literal fibers
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.FiniteWeightedGoodSourceRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion
open YMGap.Continuum.FiniteDependentKernelSelectedChoiceCongestion.SelectedChoiceCongestionCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm => by
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

/-- Filtering an attached finite carrier with nonnegative base weights can
only decrease the underlying unattached mass. -/
theorem listQSum_filter_attach_le
    {A : Type} (items : List A) (weight : A → Q')
    (weight_nonnegative : ∀ item, item ∈ items →
      (0 : Q') ≤ weight item)
    (test : {item // item ∈ items} → Bool) :
    listQSum (fun item : {item // item ∈ items} => weight item.1)
        (items.attach.filter test) ≤
      listQSum weight items := by
  exact Q'.le_trans' _ _ _
    (FiniteDependentKernelFirstSourceThinning.listQSum_filter_le_of_nonnegative
      (fun item : {item // item ∈ items} => weight item.1) test
      (fun item => weight_nonnegative item.1 item.2) items.attach)
    (Q'.le_of_eqv
      (Q'.eqv_of_eq (listQSum_attach weight items)))

/-! ## 1. Weighted column domination -/

/-- A source-to-target weight inequality on every realized channel can be
multiplied through the corresponding dependent pushed row. -/
theorem source_mul_dependentKernelPushforwardWeight_le_target_mul
    {Source Target : Type} [DecidableEq Target]
    (sourceWeight : Source → Q') (targetWeight : Target → Q')
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (source : Source) (target : Target)
    (localWeight_nonnegative : ∀ choice, choice ∈ choices source →
      (0 : Q') ≤ localWeight source choice)
    (weight_dominated : ∀ choice, choice ∈ choices source →
      target = realize source choice →
        sourceWeight source ≤ targetWeight target) :
    sourceWeight source *
        dependentKernelPushforwardWeight
          Choice choices localWeight realize source target ≤
      targetWeight target *
        dependentKernelPushforwardWeight
          Choice choices localWeight realize source target := by
  unfold dependentKernelPushforwardWeight kernelPushforwardWeight
  let sourceTerm := fun choice : Choice source =>
    sourceWeight source *
      (localWeight source choice *
        deterministicKernel (realize source) choice target)
  let targetTerm := fun choice : Choice source =>
    targetWeight target *
      (localWeight source choice *
        deterministicKernel (realize source) choice target)
  have hterms : listQSum sourceTerm (choices source) ≤
      listQSum targetTerm (choices source) := by
    apply listQSum_le_termwise_local
    intro choice hchoice
    by_cases htarget : target = realize source choice
    · have hfactor : (0 : Q') ≤
          localWeight source choice *
            deterministicKernel (realize source) choice target :=
        Q'.mul_nonneg _ _
          (localWeight_nonnegative choice hchoice)
          (deterministicKernel_nonnegative
            (realize source) choice target)
      exact Q'.mul_le_mul_of_nonneg_right _ _ _
        (weight_dominated choice hchoice htarget) hfactor
    · unfold sourceTerm targetTerm
      rw [deterministicKernel_off_image htarget]
      exact Q'.le_trans' _ 0 _
        (Q'.le_of_eqv
          (Q'.eqv_trans _ (sourceWeight source * 0) _
            (Q'.mul_eqv_congr_left (sourceWeight source) _ 0
              (Q'.mul_zero_eqv (localWeight source choice)))
            (Q'.mul_zero_eqv (sourceWeight source))))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.eqv_trans _ (targetWeight target * 0) _
              (Q'.mul_eqv_congr_left (targetWeight target) _ 0
                (Q'.mul_zero_eqv (localWeight source choice)))
              (Q'.mul_zero_eqv (targetWeight target)))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_mul_left (sourceWeight source)
          (fun choice => localWeight source choice *
            deterministicKernel (realize source) choice target)
          (choices source))))
    (Q'.le_trans' _ _ _ hterms
      (Q'.le_of_eqv
        (listQSum_mul_left (targetWeight target)
          (fun choice => localWeight source choice *
            deterministicKernel (realize source) choice target)
          (choices source))))

/-- Unweighted column capacity becomes physical weighted capacity under a
one-sided realized-channel weight comparison. -/
theorem weightedColumn_le_of_columnCapacity_of_weight_domination
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source)
    (sourceWeight : Source → Q') (targetWeight : Target → Q')
    (Choice : Source → Type)
    (choices : (source : Source) → List (Choice source))
    (localWeight : (source : Source) → Choice source → Q')
    (realize : (source : Source) → Choice source → Target)
    (target : Target)
    (targetWeight_nonnegative : (0 : Q') ≤ targetWeight target)
    (localWeight_nonnegative : ∀ source, source ∈ sources →
      ∀ choice, choice ∈ choices source →
        (0 : Q') ≤ localWeight source choice)
    (weight_dominated : ∀ source, source ∈ sources →
      ∀ choice, choice ∈ choices source →
        target = realize source choice →
          sourceWeight source ≤ targetWeight target)
    (column_capacity :
      listQSum
          (fun source => dependentKernelPushforwardWeight
            Choice choices localWeight realize source target)
          sources ≤ 1) :
    listQSum
        (fun source => sourceWeight source *
          dependentKernelPushforwardWeight
            Choice choices localWeight realize source target)
        sources ≤ targetWeight target := by
  let pushed := fun source => dependentKernelPushforwardWeight
    Choice choices localWeight realize source target
  have hterm :
      listQSum (fun source => sourceWeight source * pushed source) sources ≤
        listQSum (fun source => targetWeight target * pushed source) sources := by
    apply listQSum_le_termwise_local
    intro source hsource
    exact source_mul_dependentKernelPushforwardWeight_le_target_mul
      sourceWeight targetWeight Choice choices localWeight realize
      source target
      (localWeight_nonnegative source hsource)
      (weight_dominated source hsource)
  have hfactor :
      listQSum (fun source => targetWeight target * pushed source) sources ≈
        targetWeight target * listQSum pushed sources :=
    listQSum_mul_left (targetWeight target) pushed sources
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (listQSum pushed sources) 1 (targetWeight target)
    column_capacity targetWeight_nonnegative
  exact Q'.le_trans' _ _ _ hterm
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (Q'.mul_one_eqv (targetWeight target)))))

/-! ## 2. The finite weighted repair certificate -/

/-- A displayed repair of every source into the good target carrier.  The
factor `lambda` pays the physical weight change, and `congestion + 1` pays
the multiplicity of the repair map. -/
structure WeightedGoodSourceRepairCertificate
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (goodTargets : List Target) (targetWeight : Target → Q')
    (lambda : Q') (congestion : Nat) : Type where
  lambda_pos : (0 : Q') < lambda
  lambda_le_one : lambda ≤ (1 : Q')
  goodTargets_nodup : goodTargets.Nodup
  sourceWeight_nonnegative : ∀ source, source ∈ sources →
    (0 : Q') ≤ sourceWeight source
  targetWeight_nonnegative : ∀ target, target ∈ goodTargets →
    (0 : Q') ≤ targetWeight target
  repair : Source → Target
  repair_mem : ∀ source, source ∈ sources → repair source ∈ goodTargets
  repair_weight_floor : ∀ source, source ∈ sources →
    lambda * sourceWeight source ≤ targetWeight (repair source)
  repair_fiber_count_le : ∀ target,
    (selectedTargetFiber sources (fun _ : Source => Unit)
      (fun _ => ()) (fun source _ => repair source) target).length ≤
        congestion + 1

namespace WeightedGoodSourceRepairCertificate

/-- The selected-choice certificate consisting of the one repair arrow in
every source row. -/
def toFiniteCertificate
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) :
    SelectedChoiceCongestionCertificate
      sources (fun _ : Source => Unit) (fun _ => [()])
      (fun _ _ => (1 : Q')) (fun source _ => data.repair source)
      1 congestion where
  eta_pos := by decide
  eta_le_one := Q'.le_refl' 1
  selected := fun _ => ()
  selected_mem := by
    intro _ _
    exact List.mem_cons_self
  selected_weight_nonnegative := by
    intro _ _
    exact Q'.zero_le_one
  selected_weight_floor := by
    intro _ _
    exact Q'.le_refl' 1
  selected_weight_le_one := by
    intro _ _
    exact Q'.le_refl' 1
  fiber_count_le := data.repair_fiber_count_le

/-- The good-mass fraction supplied by the weighted repair. -/
def fraction
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) : Q' :=
  data.toFiniteCertificate.fraction * lambda

theorem fraction_pos
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) :
    (0 : Q') < data.fraction :=
  Q'.mul_pos data.toFiniteCertificate.fraction_pos data.lambda_pos

theorem fraction_le_one
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) :
    data.fraction ≤ (1 : Q') := by
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    data.toFiniteCertificate.fraction 1 lambda
    data.toFiniteCertificate.fraction_le_one
    (Q'.le_of_lt data.lambda_pos)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv lambda)) data.lambda_le_one)

def selectedRowMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion)
    (source : Source) : Q' :=
  listQSum (data.toFiniteCertificate.scaledLocalWeight source)
    (scaledChoices source)

def selectedTransportedMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) : Q' :=
  listQSum
    (fun source =>
      (lambda * sourceWeight source) * data.selectedRowMass source)
    sources

theorem finiteFraction_le_selectedRowMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion)
    (source : Source) (hsource : source ∈ sources) :
    data.toFiniteCertificate.fraction ≤ data.selectedRowMass source := by
  unfold selectedRowMass
  exact data.toFiniteCertificate.fraction_le_scaledRowMass source hsource

theorem selectedWeightedColumn_le
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion)
    (target : Target) (htarget : target ∈ goodTargets) :
    let finite := data.toFiniteCertificate
    listQSum
        (fun source => (lambda * sourceWeight source) *
          dependentKernelPushforwardWeight
            (fun _ : Source => Unit) scaledChoices
            finite.scaledLocalWeight finite.scaledRealize source target)
        sources ≤ targetWeight target := by
  dsimp only
  let finite := data.toFiniteCertificate
  apply weightedColumn_le_of_columnCapacity_of_weight_domination
    sources (fun source => lambda * sourceWeight source) targetWeight
    (fun _ : Source => Unit) scaledChoices finite.scaledLocalWeight
    finite.scaledRealize target (data.targetWeight_nonnegative target htarget)
  · intro source hsource choice _
    exact finite.scaledLocalWeight_nonnegative source hsource choice
  · intro source hsource choice _ heq
    cases choice
    have hrepair := data.repair_weight_floor source hsource
    have hrealize : finite.scaledRealize source () = data.repair source := rfl
    rw [hrealize] at heq
    exact heq ▸ hrepair
  · exact finite.scaledColumn_le_one target

theorem selectedTransportedMass_le_goodTargetMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) :
    data.selectedTransportedMass ≤ listQSum targetWeight goodTargets := by
  let finite := data.toFiniteCertificate
  exact sourceWeightedRowMass_total_le_of_dependentKernelCapacity
    sources (fun source => lambda * sourceWeight source)
    data.selectedRowMass goodTargets targetWeight
    (fun _ : Source => Unit) scaledChoices
    finite.scaledLocalWeight finite.scaledRealize
    data.goodTargets_nodup
    (fun source hsource choice _ => by
      cases choice
      exact data.repair_mem source hsource)
    (fun _ _ => Q'.eqv_refl _)
    (fun target htarget => data.selectedWeightedColumn_le target htarget)

theorem fraction_mul_sourceMass_le_selectedTransportedMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) :
    data.fraction * listQSum sourceWeight sources ≤
      data.selectedTransportedMass := by
  have hleft :
      data.fraction * listQSum sourceWeight sources ≈
        listQSum
          (fun source => data.toFiniteCertificate.fraction *
            (lambda * sourceWeight source)) sources := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv data.toFiniteCertificate.fraction lambda
        (listQSum sourceWeight sources))
      (Q'.eqv_trans _
        (data.toFiniteCertificate.fraction *
          listQSum (fun source => lambda * sourceWeight source) sources) _
        (Q'.mul_eqv_congr_left data.toFiniteCertificate.fraction _ _
          (Q'.eqv_symm
            (listQSum_mul_left lambda sourceWeight sources)))
        (Q'.eqv_symm
          (listQSum_mul_left data.toFiniteCertificate.fraction
            (fun source => lambda * sourceWeight source) sources)))
  have hterms :
      listQSum
          (fun source => data.toFiniteCertificate.fraction *
            (lambda * sourceWeight source)) sources ≤
        data.selectedTransportedMass := by
    apply listQSum_le_termwise_local
    intro source hsource
    have hnonnegative : (0 : Q') ≤ lambda * sourceWeight source :=
      Q'.mul_nonneg _ _ (Q'.le_of_lt data.lambda_pos)
        (data.sourceWeight_nonnegative source hsource)
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      data.toFiniteCertificate.fraction (data.selectedRowMass source)
      (lambda * sourceWeight source)
      (data.finiteFraction_le_selectedRowMass source hsource)
      hnonnegative
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv data.toFiniteCertificate.fraction
          (lambda * sourceWeight source)))
      hscaled
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hterms

/-- **Weighted Peierls repair theorem.**  A bounded-congestion repair into
the good target carrier proves the displayed positive good-mass density. -/
theorem fraction_mul_sourceMass_le_goodTargetMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {lambda : Q'} {congestion : Nat}
    (data : WeightedGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight lambda congestion) :
    data.fraction * listQSum sourceWeight sources ≤
      listQSum targetWeight goodTargets :=
  Q'.le_trans' _ _ _ data.fraction_mul_sourceMass_le_selectedTransportedMass
    data.selectedTransportedMass_le_goodTargetMass

#print axioms source_mul_dependentKernelPushforwardWeight_le_target_mul
#print axioms listQSum_filter_attach_le
#print axioms weightedColumn_le_of_columnCapacity_of_weight_domination
#print axioms WeightedGoodSourceRepairCertificate.toFiniteCertificate
#print axioms WeightedGoodSourceRepairCertificate.fraction_pos
#print axioms WeightedGoodSourceRepairCertificate.fraction_le_one
#print axioms WeightedGoodSourceRepairCertificate.selectedTransportedMass_le_goodTargetMass
#print axioms WeightedGoodSourceRepairCertificate.fraction_mul_sourceMass_le_goodTargetMass

end WeightedGoodSourceRepairCertificate

end YMGap.Continuum.FiniteWeightedGoodSourceRepair
