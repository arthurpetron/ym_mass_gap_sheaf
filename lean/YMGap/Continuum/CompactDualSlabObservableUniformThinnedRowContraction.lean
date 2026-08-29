/-
# A uniform surviving row channel compiles to a relative face-form gap

The first-source thinning used by the observable switching argument enforces
target-column capacity, but it can erase whole source rows when different
sources realize the same target.  One positive channel from one source proves
only a fixed-data aggregate fraction.  The correct family-level input is
therefore stronger and more local: every connected source must carry a
successful choice which survives first-source thinning, and all those choices
must have one common positive row-weight floor.

This file isolates that exact causal compiler.  A common thinned-row floor
`delta` gives

```text
  delta * connectedSourceMass <= thinnedTransportedMass,
```

hence a retained contraction with factor `1-delta`, and therefore the genuine
relative same-object face-form bound after the variance bridge.  A second
structure exposes the concrete data needed to build the floor: a successful
choice in every connected row, its first-source survival equation, and its
local weight bound.

No such source-wide family is inhabited here.  Constructive contract: finite
weighted sums, explicit dependent choices, and exact rational inequalities
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
import YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction

namespace YMGap.Continuum.CompactDualSlabObservableUniformThinnedRowContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

local instance uniformRowPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

private theorem q_lt_of_lt_of_le_local {a b c : Q'}
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  have habCross :
      a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have hbcCross :
      b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hfirst :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (b.num * (a.den : Int)) * (c.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right habCross
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hreorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (b.num * (a.den : Int)) * (c.den : Int) ≤
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right hbcCross
      (by exact_mod_cast Nat.zero_le a.den : (0 : Int) ≤ (a.den : Int))
    have hleft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (c.den : Int) (a.den : Int)]
    have hright :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hleft, hright] at hscaled
  exact Int.lt_of_mul_lt_mul_right
    (Int.lt_of_lt_of_le hfirst hsecond)
    (by exact_mod_cast Nat.zero_le b.den)

private theorem lt_add_of_pos_right_local
    (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hden : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key :
      (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hden) hden
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have efirst :
        a.num * (b.den : Int) * (a.den : Int) =
          a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [efirst]
  rw [hexpand]
  omega

private theorem one_sub_add_eqv_one_local (delta : Q') :
    ((1 : Q') + -delta) + delta ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv 1 (-delta) delta)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 ((-delta) + delta) 0
        (Q'.neg_add_self_eqv delta))
      (Q'.eqv_of_eq (Q'.add_zero' 1)))

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {selected : A}, selected ∈ items →
      value selected ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg (value head)
          (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have hmono : listQSum value tail ≤
            value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

/-! ## 1. The exact source-wide thinned-row floor -/

/-- Every connected source row retains at least `delta` after the canonical
first-source thinning.  Positivity and the upper unit bound on `delta` are
kept separate so one floor can be reused in parameter-indexed packages. -/
structure SlabObservablePairedConnectedUniformThinnedRowFloor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (delta : Q') : Type where
  row_floor : ∀ source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId,
    delta ≤ slabObservablePairedConnectedStrandThinnedRowMass
      D rootFaceId targetFaceId htarget source

namespace SlabObservablePairedConnectedUniformThinnedRowFloor

/-- Summing the pointwise row floor against the nonnegative physical source
weights retains the same fraction of the complete connected source mass. -/
theorem delta_mul_sourceMass_le_transportedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {delta : Q'}
    (data : SlabObservablePairedConnectedUniformThinnedRowFloor
      D rootFaceId targetFaceId htarget delta) :
    delta * slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId ≤
      slabObservablePairedConnectedStrandThinnedTransportedMass
        D rootFaceId targetFaceId htarget := by
  let sources := slabObservablePairedConnectedStrandSources
    D rootFaceId targetFaceId
  let sourceWeight := fun source :
      SlabObservablePairedConnectedStrandSource
        D rootFaceId targetFaceId =>
    slabObservableTwoReplicaPairWeight D source.1
  let rowMass := fun source :
      SlabObservablePairedConnectedStrandSource
        D rootFaceId targetFaceId =>
    slabObservablePairedConnectedStrandThinnedRowMass
      D rootFaceId targetFaceId htarget source
  have hsource : listQSum sourceWeight sources ≈
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId := by
    apply Q'.eqv_of_eq
    unfold sources sourceWeight
      slabObservablePairedConnectedStrandSources
      slabObservablePairedConnectedSourceMass
    exact listQSum_attach
      (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId)
  have hleft :
      delta * slabObservablePairedConnectedSourceMass
          D rootFaceId targetFaceId ≈
        listQSum (fun source => delta * sourceWeight source) sources := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left delta _ _ (Q'.eqv_symm hsource))
      (Q'.eqv_symm (listQSum_mul_left delta sourceWeight sources))
  have hterms :
      listQSum (fun source => delta * sourceWeight source) sources ≤
        listQSum (fun source => sourceWeight source * rowMass source)
          sources := by
    apply listQSum_le_termwise_local
    intro source _
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      delta (rowMass source) (sourceWeight source)
      (data.row_floor source)
      (slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv delta (sourceWeight source)))
      hscaled
  unfold slabObservablePairedConnectedStrandThinnedTransportedMass
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hterms

/-- A positive source-wide row floor is already the retained-contraction
certificate; no quotient by a volume-dependent aggregate mass is needed. -/
def toRetainedContraction
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {delta : Q'}
    (data : SlabObservablePairedConnectedUniformThinnedRowFloor
      D rootFaceId targetFaceId htarget delta)
    (hdeltaPos : (0 : Q') < delta)
    (hdeltaLeOne : delta ≤ (1 : Q')) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId where
  fraction := delta
  fraction_pos := hdeltaPos
  fraction_le_one := hdeltaLeOne
  disconnected_add_fraction_mul_connected_le_target := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.le_refl' _)
        data.delta_mul_sourceMass_le_transportedMass)
      (slabObservablePairedSplitTransportedMass_le_target
        D rootFaceId targetFaceId htarget)

/-- After exact reflection and the variance bridge, the common thinned-row
floor is a genuine relative form gap for the centered face indicator. -/
theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    {delta : Q'}
    (data : SlabObservablePairedConnectedUniformThinnedRowFloor
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)
      (slabFaceReflectId_physical
        (mem_centralLowerFaceIds.mp hroot).1) delta)
    (hdeltaPos : (0 : Q') < delta)
    (hdeltaLeOne : delta ≤ (1 : Q')) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≤
      ((1 : Q') + -delta) *
        centralPhysicalWeightedInner
          D.coupling D.coupling_nonnegative D.cutoff D.half
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value)
          (centralPhysicalCenteredObservable
            D.coupling D.coupling_nonnegative D.cutoff D.half
            (slabPhysicalFacePositiveUnitObservable rootFaceId).value) := by
  exact
    CompactDualSlabObservableFaceVarianceBridge.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
      D hroot (data.toRetainedContraction hdeltaPos hdeltaLeOne)

end SlabObservablePairedConnectedUniformThinnedRowFloor

/-! ## 2. The observable, connected path through the compiler -/

/-- Concrete source-wise data sufficient to build the uniform row floor.
The `first_source` field is the load-bearing collision-control equation: the
chosen successful target for each connected source must select that source,
not an earlier competing row. -/
structure SlabObservablePairedConnectedSurvivingChoiceFloor
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (delta : Q') : Type where
  choice : ∀ source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId,
    SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source
  choice_mem : ∀ source,
    choice source ∈ slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId source
  first_source : ∀ source,
    firstSourceForTarget
      (SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget)
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget source (choice source))
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId) = some source
  choice_weight_floor : ∀ source,
    delta ≤ slabObservablePairedConnectedStrandWeight
      D rootFaceId targetFaceId source (choice source)

namespace SlabObservablePairedConnectedSurvivingChoiceFloor

/-- One collision-free positive choice in every row constructs the exact
uniform thinned-row floor consumed above. -/
def toUniformThinnedRowFloor
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    {delta : Q'}
    (data : SlabObservablePairedConnectedSurvivingChoiceFloor
      D rootFaceId targetFaceId htarget delta) :
    SlabObservablePairedConnectedUniformThinnedRowFloor
      D rootFaceId targetFaceId htarget delta where
  row_floor := by
    intro source
    have hselected :
        slabObservablePairedConnectedStrandThinnedWeight
            D rootFaceId targetFaceId htarget source
              (data.choice source) =
          slabObservablePairedConnectedStrandWeight
            D rootFaceId targetFaceId source (data.choice source) := by
      unfold slabObservablePairedConnectedStrandThinnedWeight
        firstSourceThinnedWeight
      simp only [if_pos (data.first_source source)]
    have hchoice : delta ≤
        slabObservablePairedConnectedStrandThinnedWeight
          D rootFaceId targetFaceId htarget source
            (data.choice source) := by
      rw [hselected]
      exact data.choice_weight_floor source
    unfold slabObservablePairedConnectedStrandThinnedRowMass
    exact Q'.le_trans' _ _ _ hchoice
      (listQSum_member_le_nonnegative_local
        (slabObservablePairedConnectedStrandThinnedWeight
          D rootFaceId targetFaceId htarget source)
        (fun choice =>
          slabObservablePairedConnectedStrandThinnedWeight_nonnegative
            D rootFaceId targetFaceId htarget source choice)
        (slabObservablePairedConnectedStrandChoices
          D rootFaceId targetFaceId source)
        (data.choice_mem source))

end SlabObservablePairedConnectedSurvivingChoiceFloor

/-! ## 3. A common path over changing finite data -/

/-- The exact dynamic certificate needed for a common observable face rate
over a parameter-indexed family of finite slabs.  This is deliberately only
the finite same-object input; graph-norm convergence and continuum
identification remain separate later compilers. -/
structure SlabObservableReflectedUniformRowPath
    (Index : Type) (datum : Index → SlabPhysicalData)
    (rootFaceId : Index → Nat) (delta : Q') : Type where
  delta_pos : (0 : Q') < delta
  delta_le_one : delta ≤ (1 : Q')
  root_lower : ∀ index,
    rootFaceId index ∈ centralLowerFaceIds (datum index).half
  row_floor : ∀ index,
    SlabObservablePairedConnectedUniformThinnedRowFloor
      (datum index) (rootFaceId index)
      (slabFaceReflectId (datum index).extent (rootFaceId index))
      (slabFaceReflectId_physical
        (mem_centralLowerFaceIds.mp (root_lower index)).1)
      delta

namespace SlabObservableReflectedUniformRowPath

theorem factor_nonnegative
    {Index : Type} {datum : Index → SlabPhysicalData}
    {rootFaceId : Index → Nat} {delta : Q'}
    (path : SlabObservableReflectedUniformRowPath
      Index datum rootFaceId delta) :
    (0 : Q') ≤ (1 : Q') + -delta :=
  Q'.sub_nonneg_of_le path.delta_le_one

theorem factor_lt_one
    {Index : Type} {datum : Index → SlabPhysicalData}
    {rootFaceId : Index → Nat} {delta : Q'}
    (path : SlabObservableReflectedUniformRowPath
      Index datum rootFaceId delta) :
    (1 : Q') + -delta < (1 : Q') :=
  q_lt_of_lt_of_le_local
    (lt_add_of_pos_right_local
      ((1 : Q') + -delta) delta path.delta_pos)
    (Q'.le_of_eqv (one_sub_add_eqv_one_local delta))

/-- Every member of a common-row-floor path satisfies the same strict
same-object face-form bound.  The conclusion names the common factor and the
finite datum explicitly; no limiting identification is hidden here. -/
theorem sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    {Index : Type} {datum : Index → SlabPhysicalData}
    {rootFaceId : Index → Nat} {delta : Q'}
    (path : SlabObservableReflectedUniformRowPath
      Index datum rootFaceId delta)
    (index : Index) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        (datum index) (rootFaceId index) ≤
      ((1 : Q') + -delta) *
        centralPhysicalWeightedInner
          (datum index).coupling (datum index).coupling_nonnegative
          (datum index).cutoff (datum index).half
          (centralPhysicalCenteredObservable
            (datum index).coupling (datum index).coupling_nonnegative
            (datum index).cutoff (datum index).half
            (slabPhysicalFacePositiveUnitObservable
              (rootFaceId index)).value)
          (centralPhysicalCenteredObservable
            (datum index).coupling (datum index).coupling_nonnegative
            (datum index).cutoff (datum index).half
            (slabPhysicalFacePositiveUnitObservable
              (rootFaceId index)).value) := by
  exact
    SlabObservablePairedConnectedUniformThinnedRowFloor.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
      (datum index) (path.root_lower index) (path.row_floor index)
      path.delta_pos path.delta_le_one

end SlabObservableReflectedUniformRowPath

#print axioms SlabObservablePairedConnectedUniformThinnedRowFloor.delta_mul_sourceMass_le_transportedMass
#print axioms SlabObservablePairedConnectedUniformThinnedRowFloor.toRetainedContraction
#print axioms SlabObservablePairedConnectedUniformThinnedRowFloor.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
#print axioms SlabObservablePairedConnectedSurvivingChoiceFloor.toUniformThinnedRowFloor
#print axioms SlabObservableReflectedUniformRowPath.factor_lt_one
#print axioms SlabObservableReflectedUniformRowPath.sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm

end YMGap.Continuum.CompactDualSlabObservableUniformThinnedRowContraction
