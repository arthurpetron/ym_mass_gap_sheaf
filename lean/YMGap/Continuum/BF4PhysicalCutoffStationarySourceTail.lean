/-
# Stationary positive-source tail for physical BF4 cutoff removal

The last residual in the moving-core Markov Cauchy compiler is the stationary
row-marginal mass outside an old positive source carrier.  This file recodes
that complement as a single cutoff-stable lower slab event.

At its own base cutoff the event has exactly zero stationary mass: every state
in the retained stationary carrier is both base-bounded and has positive base
row marginal.  At a later cutoff, the sharp bounded-observable tail therefore
bounds its mass by the complete corrected-slab new-label increment.  Moving
the base beyond the existing retained-cutoff schedule only decreases that
increment.

Consequently the stationary source-tail datum is inhabited, and the existing
core--shell compiler yields unconditional atomic and dense Markov cutoff
Cauchy data at fixed nome and finite half-extent.

## Axiom gate

Only finite Boolean filtering, exact rational algebra, and the constructive
corrected-slab cutoff schedule are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffConditionalCoreModulus
import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination

namespace YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffConditionalCoreCauchy
open YMGap.Continuum.BF4PhysicalCutoffConditionalCoreModulus
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The positive-source complement as one unit observable -/

def centralPhysicalPositiveSourceOutsideB
    (w : Q') (hw : (0 : Q') <= w)
    (base half : Nat) (state : EdgeLabelling) : Bool :=
  !(
    labelWithinB base (centralLowerFaceIds half) state &&
      decide ((0 : Q') <
        centralPhysicalRowMarginal w hw base half state))

def centralPhysicalPositiveSourceOutsideIndicator
    (w : Q') (hw : (0 : Q') <= w)
    (base half : Nat) (state : EdgeLabelling) : Q' :=
  if centralPhysicalPositiveSourceOutsideB
      w hw base half state then 1 else 0

def centralPhysicalPositiveSourceOutsideObservable
    (w : Q') (hw : (0 : Q') <= w)
    (base half : Nat) : CentralPhysicalUnitObservable where
  value := centralPhysicalPositiveSourceOutsideIndicator
    w hw base half
  nonnegative := by
    intro state
    unfold centralPhysicalPositiveSourceOutsideIndicator
    cases centralPhysicalPositiveSourceOutsideB w hw base half state <;>
      decide
  le_one := by
    intro state
    unfold centralPhysicalPositiveSourceOutsideIndicator
    cases centralPhysicalPositiveSourceOutsideB w hw base half state <;>
      decide

private theorem row_mul_outsideIndicator_eqv_masked
    (w : Q') (hw : (0 : Q') <= w)
    (cutoff base half : Nat) (state : EdgeLabelling) :
    centralPhysicalRowMarginal w hw cutoff half state *
        centralPhysicalPositiveSourceOutsideIndicator
          w hw base half state ≈
      finiteMaskedValue
        (centralPhysicalPositiveSourceOutsideB w hw base half)
        (centralPhysicalRowMarginal w hw cutoff half) state := by
  unfold centralPhysicalPositiveSourceOutsideIndicator finiteMaskedValue
  cases centralPhysicalPositiveSourceOutsideB w hw base half state with
  | false => exact Q'.mul_zero_eqv _
  | true => exact Q'.mul_one_eqv _

/-- The compiler's literal filtered source-shell mass is exactly the
stationary mean of the source-complement indicator. -/
theorem centralPhysicalRowMarginalOutsideBase_eq_stationaryMean
    (w : Q') (hw : (0 : Q') <= w)
    (cutoff half base : Nat) :
    centralPhysicalRowMarginalOutsideBase
        w hw cutoff half base ≈
      centralPhysicalStationaryMean
        w hw cutoff half
        (centralPhysicalPositiveSourceOutsideObservable
          w hw base half).value := by
  refine Q'.eqv_trans _
    (listQSum
      (finiteMaskedValue
        (fun state => !(
          labelWithinB base (centralLowerFaceIds half) state &&
            decide ((0 : Q') <
              centralPhysicalRowMarginal w hw base half state)))
        (centralPhysicalRowMarginal w hw cutoff half))
      (centralPositiveHalfStates w hw cutoff half)) _ ?_ ?_
  · unfold centralPhysicalRowMarginalOutsideBase
    exact Q'.eqv_symm
      (listQSum_finiteMaskedValue_eqv_filter
        (fun state => !(
          labelWithinB base (centralLowerFaceIds half) state &&
            decide ((0 : Q') <
              centralPhysicalRowMarginal w hw base half state)))
        (centralPhysicalRowMarginal w hw cutoff half)
        (centralPositiveHalfStates w hw cutoff half))
  · unfold centralPhysicalStationaryMean
      centralPhysicalPositiveSourceOutsideObservable
    apply listQSum_congr
    intro state
    exact Q'.eqv_symm
      (row_mul_outsideIndicator_eqv_masked
        w hw cutoff base half state)

/-! ## 2. The anchor event is empty -/

private theorem filter_false_on_all_local
    {A : Type} (test : A -> Bool) :
    forall items : List A,
      (forall item, item ∈ items -> test item = false) ->
      items.filter test = []
  | [], _ => rfl
  | head :: tail, hfalse => by
      have hhead := hfalse head List.mem_cons_self
      have htail : forall item, item ∈ tail -> test item = false :=
        fun item hitem =>
          hfalse item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead, Bool.false_eq_true, if_false]
      exact filter_false_on_all_local test tail htail

private theorem centralPhysicalPositiveSourceOutside_filter_self_empty
    (w : Q') (hw : (0 : Q') <= w)
    (base half : Nat) :
    (centralPositiveHalfStates w hw base half).filter
        (centralPhysicalPositiveSourceOutsideB w hw base half) = [] := by
  apply filter_false_on_all_local
  intro state hstate
  have hparts := mem_centralPositiveHalfStates_iff.mp hstate
  have hwithin : labelWithinB base
      (centralLowerFaceIds half) state = true := by
    apply (labelWithinB_true_iff
      base (centralLowerFaceIds half) state).mpr
    unfold centralHalfStates at hparts
    exact (boundedEdgeLabellings_sound
      base (centralLowerFaceIds half) state hparts.1).1
  unfold centralPhysicalPositiveSourceOutsideB
  simp only [hwithin, hparts.2, decide_true, Bool.true_and, Bool.not_true]

theorem centralPhysicalRowMarginalOutsideBase_self_eqv_zero
    (w : Q') (hw : (0 : Q') <= w)
    (base half : Nat) :
    centralPhysicalRowMarginalOutsideBase
        w hw base half base ≈ 0 := by
  change listQSum (centralPhysicalRowMarginal w hw base half)
    ((centralPositiveHalfStates w hw base half).filter
      (centralPhysicalPositiveSourceOutsideB w hw base half)) ≈ 0
  rw [centralPhysicalPositiveSourceOutside_filter_self_empty]
  exact Q'.eqv_refl 0

/-! ## 3. Corrected-slab tail bound -/

/-- Stationary mass outside the positive source carrier at `base` is bounded
by the complete new-label mass between `base` and any later cutoff. -/
theorem centralPhysicalRowMarginalOutsideBase_le_increment
    {w : Q'} (hw : (0 : Q') <= w)
    {base later half : Nat} (hbaseLater : base <= later) :
    centralPhysicalRowMarginalOutsideBase
        w hw later half base <=
      slabParametricKCutoffIncrement
        w base later (centralExtent half) := by
  let observable := centralPhysicalPositiveSourceOutsideObservable
    w hw base half
  let slabObservable := centralLowerSlabUnitObservable half observable
  have habs :=
    slabNomeCutoffBoundedObservableExpectation_abs_le_increment
      hw hbaseLater slabObservable
  have hbaseStationary :=
    centralPhysicalRowMarginalOutsideBase_eq_stationaryMean
      w hw base half base
  have hlaterStationary :=
    centralPhysicalRowMarginalOutsideBase_eq_stationaryMean
      w hw later half base
  have hbaseBridge :=
    centralPhysicalStationaryMean_eq_slabExpectation
      w hw base half observable
  have hlaterBridge :=
    centralPhysicalStationaryMean_eq_slabExpectation
      w hw later half observable
  have hbaseZero := centralPhysicalRowMarginalOutsideBase_self_eqv_zero
    w hw base half
  have hbaseExpectationZero :
      slabNomeCutoffBoundedObservableExpectation
          w hw base (centralExtent half) slabObservable ≈ 0 :=
    Q'.eqv_trans _
      (centralPhysicalStationaryMean
        w hw base half observable.value) _
      (Q'.eqv_symm hbaseBridge)
      (Q'.eqv_trans _
        (centralPhysicalRowMarginalOutsideBase w hw base half base) _
        (Q'.eqv_symm hbaseStationary) hbaseZero)
  have hlaterExpectation :
      centralPhysicalRowMarginalOutsideBase w hw later half base ≈
        slabNomeCutoffBoundedObservableExpectation
          w hw later (centralExtent half) slabObservable :=
    Q'.eqv_trans _
      (centralPhysicalStationaryMean
        w hw later half observable.value) _
      hlaterStationary hlaterBridge
  have habsQ :
      Q'.abs
          (slabNomeCutoffBoundedObservableExpectation
              w hw base (centralExtent half) slabObservable +
            -slabNomeCutoffBoundedObservableExpectation
              w hw later (centralExtent half) slabObservable) <=
        slabParametricKCutoffIncrement
          w base later (centralExtent half) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs _)))
      habs
  have hlaterLe :
      slabNomeCutoffBoundedObservableExpectation
          w hw later (centralExtent half) slabObservable <=
        slabNomeCutoffBoundedObservableExpectation
            w hw base (centralExtent half) slabObservable +
          slabParametricKCutoffIncrement
            w base later (centralExtent half) := by
    apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm _ _))
      habsQ
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hlaterExpectation) ?_
  refine Q'.le_trans' _ _ _ hlaterLe ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hbaseExpectationZero)
      (QPoly.q_zero_add_eqv _))

/-! ## 4. Executable source-tail schedule and full Cauchy data -/

def centralPhysicalStationarySourceTailBase
    (w : Q') (half : Nat) (epsilon : Q') : Nat :=
  max (centralPhysicalUniformRowFloorCutoff w half)
    (centralPhysicalTargetShellCutoff
      w half (HalfPow.half * epsilon))

theorem centralPhysicalUniformRowFloorCutoff_le_stationarySourceTailBase
    (w : Q') (half : Nat) (epsilon : Q') :
    centralPhysicalUniformRowFloorCutoff w half <=
      centralPhysicalStationarySourceTailBase w half epsilon := by
  unfold centralPhysicalStationarySourceTailBase
  exact Nat.le_max_left _ _

theorem centralPhysicalTargetShellCutoff_le_stationarySourceTailBase
    (w : Q') (half : Nat) (epsilon : Q') :
    centralPhysicalTargetShellCutoff
        w half (HalfPow.half * epsilon) <=
      centralPhysicalStationarySourceTailBase w half epsilon := by
  unfold centralPhysicalStationarySourceTailBase
  exact Nat.le_max_right _ _

theorem centralPhysicalRowMarginalOutside_stationarySourceTailBase_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {later : Nat}
    (hlater : centralPhysicalStationarySourceTailBase
      w half epsilon <= later) :
    centralPhysicalRowMarginalOutsideBase
        w (Q'.le_of_lt hw0) later half
        (centralPhysicalStationarySourceTailBase w half epsilon) <=
      HalfPow.half * epsilon := by
  let scheduled := centralPhysicalTargetShellCutoff
    w half (HalfPow.half * epsilon)
  let base := centralPhysicalStationarySourceTailBase w half epsilon
  have hscheduleBase : scheduled <= base := by
    unfold scheduled base
    exact centralPhysicalTargetShellCutoff_le_stationarySourceTailBase
      w half epsilon
  have hscheduleLater : scheduled <= later :=
    Nat.le_trans hscheduleBase hlater
  have hshell := centralPhysicalRowMarginalOutsideBase_le_increment
    (half := half) (Q'.le_of_lt hw0) hlater
  have hincrementMono := slabParametricKCutoffIncrement_antitone_base
    (extent := centralExtent half)
    (Q'.le_of_lt hw0) hscheduleBase hlater
  have htolerance :
      slabParametricKCutoffIncrement
          w scheduled later (centralExtent half) <=
        HalfPow.half * epsilon := by
    unfold scheduled centralPhysicalTargetShellCutoff
    exact slabPhysicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 (centralExtent half)
      (ExpNeg.half_mul_pos epsilon hepsilon) hscheduleLater
  exact Q'.le_trans' _ _ _ hshell
    (Q'.le_trans' _ _ _ hincrementMono htolerance)

/-- The last residual record is now inhabited by one observable-independent
source-core schedule. -/
def centralPhysicalStationaryPositiveSourceTailData
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat) :
    CentralPhysicalStationaryPositiveSourceTailData hw0 hw1 half where
  base := fun _observable epsilon =>
    centralPhysicalStationarySourceTailBase w half epsilon
  uniformFloorCutoff_le_base := by
    intro _observable epsilon
    exact centralPhysicalUniformRowFloorCutoff_le_stationarySourceTailBase
      w half epsilon
  stageRate := fun _observable epsilon =>
    centralPhysicalStationarySourceTailBase w half epsilon
  shellMass := by
    intro _observable epsilon hepsilon cutoff hcutoff
    exact centralPhysicalRowMarginalOutside_stationarySourceTailBase_le
      hw0 hw1 half hepsilon hcutoff

def centralPhysicalAtomicMarkovCoreTailCauchyData
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat) :=
  (centralPhysicalStationaryPositiveSourceTailData
    hw0 hw1 half).toCoreTailCauchyData

def centralPhysicalAtomicMarkovCauchyData
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat) :=
  (centralPhysicalStationaryPositiveSourceTailData
    hw0 hw1 half).toAtomicCauchyData

def centralPhysicalDenseMarkovCauchyData
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat) :=
  (centralPhysicalStationaryPositiveSourceTailData
    hw0 hw1 half).toDenseCauchyData

/-! ## Axiom audit -/

#print axioms centralPhysicalPositiveSourceOutsideObservable
#print axioms centralPhysicalRowMarginalOutsideBase_eq_stationaryMean
#print axioms centralPhysicalRowMarginalOutsideBase_le_increment
#print axioms centralPhysicalRowMarginalOutside_stationarySourceTailBase_le
#print axioms centralPhysicalStationaryPositiveSourceTailData
#print axioms centralPhysicalAtomicMarkovCoreTailCauchyData
#print axioms centralPhysicalAtomicMarkovCauchyData
#print axioms centralPhysicalDenseMarkovCauchyData

end YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
