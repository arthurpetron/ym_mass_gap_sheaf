/-
# Core--shell compiler for atomic physical BF4 Markov Cauchy data

Uniform pointwise convergence on every edge labelling is stronger than the
moving representation-cutoff problem naturally supplies.  This file replaces
that sufficient condition by the causal decomposition seen by each finite GNS
approximation.

Choose an old cutoff carrier.  On its finite core, require a pointwise squared
bound between two later recoded atomic Markov images.  Outside that core, use
only that both images are `[0,1]`-valued, so their squared difference is at
most one, and pay the stationary row-marginal mass of the shell.  Exact finite
partition and normalization then give

`finite distance^2 <= core error + shell mass`.

A certificate that pays each term with half of `epsilon` constructs the atomic
cross-cutoff Cauchy data and hence the full dense datum used by the adaptive
completed transfer.

No core convergence or shell-tail certificate is inhabited here.  The point
is to separate two mathematically different analytic tasks and expose both as
finite rational estimates.

## Axiom gate

Only finite Boolean carrier partitions, positivity and normalization of the
physical row marginal, unit-interval bounds, exact rational algebra, and the
proved finite-stage GNS bridge are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit stationary shell -/

/-- Stationary mass, at one finite approximation cutoff, outside the old
edgewise representation carrier `base`. -/
def centralPhysicalRowMarginalOutsideBase
    (w : Q') (hw : (0 : Q') <= w)
    (cutoff half base : Nat) : Q' :=
  listQSum
    (centralPhysicalRowMarginal w hw cutoff half)
    ((centralPositiveHalfStates w hw cutoff half).filter
      (fun state => !(labelWithinB base
        (centralLowerFaceIds half) state)))

/-! ## 2. Unit-interval and finite core--shell estimates -/

private theorem listQSum_filter_le_nonnegative
    {A : Type} (value : A -> Q') (test : A -> Bool)
    (hvalue : forall item, (0 : Q') <= value item) :
    forall items : List A,
      listQSum value (items.filter test) <= listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_nonnegative value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          have hmono : listQSum value tail <=
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
              (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

private theorem unit_sub_sq_le_one
    (left right :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (state : EdgeLabelling) :
    let difference := left.value state + -(right.value state)
    difference * difference <= (1 : Q') := by
  let difference := left.value state + -(right.value state)
  have hone_le_right_add : (1 : Q') <= right.value state + 1 := by
    have h := Q'.add_le_add_right
      (0 : Q') (right.value state) 1 (right.nonnegative state)
    rwa [Q'.zero_add'] at h
  have hone_le_left_add : (1 : Q') <= left.value state + 1 := by
    have h := Q'.add_le_add_right
      (0 : Q') (left.value state) 1 (left.nonnegative state)
    rwa [Q'.zero_add'] at h
  have hforward : left.value state <= right.value state + 1 :=
    Q'.le_trans' _ _ _ (left.le_one state) hone_le_right_add
  have hbackward : right.value state <= left.value state + 1 :=
    Q'.le_trans' _ _ _ (right.le_one state) hone_le_left_add
  have habs : Q'.abs difference <= (1 : Q') :=
    CReal.abs_sub_le_of_bounds hforward hbackward
  have hsquare : difference * difference <= (1 : Q') * 1 := by
    refine Q'.le_trans' _ _ _ (Q'.le_abs_self _) ?_
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le difference difference) ?_
    exact Q'.mul_le_mul_of_nonneg
      habs habs Q'.zero_le_one (Q'.abs_nonneg difference)
  exact Q'.le_trans' _ _ _ hsquare
    (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- A finite physical GNS distance is bounded by its old-carrier pointwise
error plus the stationary mass of the complementary shell. -/
theorem centralPhysicalFiniteUnitDistSq_le_core_add_shell
    {w : Q'} (hw : (0 : Q') <= w)
    (cutoff half base : Nat)
    (left right :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (coreError : Q') (hcoreError : (0 : Q') <= coreError)
    (hcore : forall state,
      (forall edge, edge ∉ centralLowerFaceIds half -> state edge = 0) ->
      labelWithinB base (centralLowerFaceIds half) state = true ->
      let difference := left.value state + -(right.value state)
      difference * difference <= coreError) :
    (centralPhysicalSmulGNS w hw cutoff half).toGNSData.distSqQ
        left.value right.value <=
      coreError +
        centralPhysicalRowMarginalOutsideBase
          w hw cutoff half base := by
  let states := centralPositiveHalfStates w hw cutoff half
  let row := centralPhysicalRowMarginal w hw cutoff half
  let test := fun state =>
    labelWithinB base (centralLowerFaceIds half) state
  let difference := fun state => left.value state + -(right.value state)
  let weightedSquare := fun state =>
    row state * (difference state * difference state)
  change listQSum weightedSquare states <=
    coreError + centralPhysicalRowMarginalOutsideBase
      w hw cutoff half base
  have hsplit := listQSum_filter_partition weightedSquare test states
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  apply Q'.add_le_add
  · have hpoint : listQSum weightedSquare (states.filter test) <=
        listQSum (fun state => row state * coreError)
          (states.filter test) := by
      apply listQSum_mono
      intro state hstate
      have hpositive := (List.mem_filter.mp hstate).1
      have hcutoffCarrier :=
        (mem_centralPositiveHalfStates_iff.mp hpositive).1
      have hsupport :=
        (boundedEdgeLabellings_sound cutoff
          (centralLowerFaceIds half) state hcutoffCarrier).2
      exact Q'.mul_le_mul_of_nonneg_left _ _ _
        (hcore state hsupport (List.mem_filter.mp hstate).2)
        (centralPhysicalRowMarginal_nonnegative hw cutoff half state)
    refine Q'.le_trans' _ _ _ hpoint ?_
    refine Q'.le_trans' _
      (listQSum row (states.filter test) * coreError) _
      (Q'.le_of_eqv
        (listQSum_mul_right row coreError (states.filter test))) ?_
    have hmass : listQSum row (states.filter test) <= (1 : Q') :=
      Q'.le_trans' _ _ _
        (listQSum_filter_le_nonnegative row test
          (fun state =>
            centralPhysicalRowMarginal_nonnegative hw cutoff half state)
          states)
        (Q'.le_of_eqv
          (centralPositiveRowMarginal_total_one w hw cutoff half))
    exact Q'.le_trans' _ ((1 : Q') * coreError) _
      (Q'.mul_le_mul_of_nonneg_right _ _ coreError hmass hcoreError)
      (Q'.le_of_eqv (Q'.one_mul_eqv coreError))
  · change listQSum weightedSquare
        (states.filter (fun state => !(test state))) <=
      listQSum row (states.filter (fun state => !(test state)))
    apply listQSum_mono
    intro state _
    exact Q'.le_trans' _ (row state * (1 : Q')) _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (unit_sub_sq_le_one left right state)
        (centralPhysicalRowMarginal_nonnegative hw cutoff half state))
      (Q'.le_of_eqv (Q'.mul_one_eqv (row state)))

/-! ## 3. Eventual finite estimates give the limiting atomic distance -/

private theorem leEv_of_eventual_approx_le
    {left right : CReal} (rate : Nat)
    (h : forall cutoff, rate <= cutoff ->
      left.approx cutoff <= right.approx cutoff) :
    CReal.leEv left right := by
  intro epsilon hepsilon
  exact ⟨rate, fun cutoff hcutoff =>
    Q'.le_trans' _ _ _ (h cutoff hcutoff)
      (Q'.add_le_self_of_nonneg
        (right.approx cutoff) epsilon (Q'.le_of_lt hepsilon))⟩

/-- Core pointwise control and eventual shell-mass control bound the
cutoff-removed squared distance of two recoded atomic images. -/
theorem centralPhysicalAtomicMarkovDistSq_le_core_add_shell
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half base first second : Nat)
    (observable :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (coreError shellError : Q')
    (hcoreError : (0 : Q') <= coreError)
    (stageRate : Nat)
    (hcore : forall state,
      (forall edge, edge ∉ centralLowerFaceIds half -> state edge = 0) ->
      labelWithinB base (centralLowerFaceIds half) state = true ->
      let left := centralPhysicalMarkovCutoffUnitObservable
        (Q'.le_of_lt hw0) first half observable
      let right := centralPhysicalMarkovCutoffUnitObservable
        (Q'.le_of_lt hw0) second half observable
      let difference := left.value state + -(right.value state)
      difference * difference <= coreError)
    (hshell : forall cutoff, stageRate <= cutoff ->
      centralPhysicalRowMarginalOutsideBase
        w (Q'.le_of_lt hw0) cutoff half base <= shellError) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) first half (atom observable))
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) second half (atom observable)))
      (CReal.ofQ' (coreError + shellError)) := by
  apply leEv_of_eventual_approx_le stageRate
  intro cutoff hcutoff
  have hstage := physicalLinearDistSq_approx_eqv_stage
    hw0 hw1 half cutoff
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) first half (atom observable))
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) second half (atom observable))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hstage) ?_
  have hfinite := centralPhysicalFiniteUnitDistSq_le_core_add_shell
    (Q'.le_of_lt hw0) cutoff half base
    (centralPhysicalMarkovCutoffUnitObservable
      (Q'.le_of_lt hw0) first half observable)
    (centralPhysicalMarkovCutoffUnitObservable
      (Q'.le_of_lt hw0) second half observable)
    coreError hcoreError hcore
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.add_le_add_left coreError _ shellError (hshell cutoff hcutoff))

/-! ## 4. The exact core--shell residual and its contraction -/

/-- Finite core convergence plus stationary shell tightness, with equal
half-epsilon budgets.  This is the moving-carrier input sufficient for all
atomic Markov Cauchy moduli. -/
structure CentralPhysicalAtomicMarkovCoreTailCauchyData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  base :
    YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable ->
      Q' -> Nat
  actionRate :
    YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable ->
      Q' -> Nat
  base_le_actionRate : forall observable epsilon,
    base observable epsilon <= actionRate observable epsilon
  stageRate :
    YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable ->
      Q' -> Nat
  coreSq : forall
    (observable :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall first second,
      actionRate observable epsilon <= first ->
      actionRate observable epsilon <= second ->
    forall state,
      (forall edge, edge ∉ centralLowerFaceIds half -> state edge = 0) ->
      labelWithinB (base observable epsilon)
        (centralLowerFaceIds half) state = true ->
      let left := centralPhysicalMarkovCutoffUnitObservable
        (Q'.le_of_lt hw0) first half observable
      let right := centralPhysicalMarkovCutoffUnitObservable
        (Q'.le_of_lt hw0) second half observable
      let difference := left.value state + -(right.value state)
      difference * difference <= HalfPow.half * epsilon
  shellMass : forall
    (observable :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall cutoff, stageRate observable epsilon <= cutoff ->
      centralPhysicalRowMarginalOutsideBase
        w (Q'.le_of_lt hw0) cutoff half (base observable epsilon) <=
          HalfPow.half * epsilon

/-- Core--shell Cauchy data construct the atomic moduli. -/
def CentralPhysicalAtomicMarkovCoreTailCauchyData.toAtomicCauchyData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalAtomicMarkovCoreTailCauchyData hw0 hw1 half) :
    CentralPhysicalLinearMarkovAtomicCauchyData hw0 hw1 half where
  modulus observable :=
    { rate := data.actionRate observable
      cauchy := by
        intro epsilon hepsilon first second hfirst hsecond
        have hbound := centralPhysicalAtomicMarkovDistSq_le_core_add_shell
          hw0 hw1 half (data.base observable epsilon) first second observable
          (HalfPow.half * epsilon) (HalfPow.half * epsilon)
          (Q'.mul_nonneg HalfPow.half epsilon
            HalfPow.half_nonneg (Q'.le_of_lt hepsilon))
          (data.stageRate observable epsilon)
          (data.coreSq observable epsilon hepsilon
            first second hfirst hsecond)
          (data.shellMass observable epsilon hepsilon)
        exact CReal.leEv_trans hbound
          (CReal.leEv_of_le
            (CReal.ofQ'_le_ofQ'
              (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))) }

/-- Core--shell Cauchy data therefore construct the exact dense pointwise
datum consumed by the adaptive completed-transfer and gap chain. -/
def CentralPhysicalAtomicMarkovCoreTailCauchyData.toDenseCauchyData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (data : CentralPhysicalAtomicMarkovCoreTailCauchyData hw0 hw1 half) :
    CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half :=
  data.toAtomicCauchyData.toDenseCauchyData

/-! ## Axiom audit -/

#print axioms centralPhysicalRowMarginalOutsideBase
#print axioms centralPhysicalFiniteUnitDistSq_le_core_add_shell
#print axioms centralPhysicalAtomicMarkovDistSq_le_core_add_shell
#print axioms CentralPhysicalAtomicMarkovCoreTailCauchyData
#print axioms CentralPhysicalAtomicMarkovCoreTailCauchyData.toAtomicCauchyData
#print axioms CentralPhysicalAtomicMarkovCoreTailCauchyData.toDenseCauchyData

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
