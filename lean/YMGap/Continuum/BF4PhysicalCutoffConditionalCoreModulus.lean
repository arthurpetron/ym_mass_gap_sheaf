/-
# An executable modulus for the physical BF4 conditional core

The pointwise quotient estimate is now inhabited, but the atomic Cauchy
compiler requests a squared error at an explicit action rate.  This file
allocates the quotient budget without a circular cutoff choice.

The stationary source core is selected first.  Its finite positive-row
minimum supplies the denominator floor.  Only then is an independent target
core enlarged to pay the two target-shell tolerances, and the old-row `l1`
schedule is placed beyond it.  One quarter of the quotient budget pays the
old row and one eighth pays each target shell; doubling the resulting common
error consumes exactly the quotient budget.

The entire conditional-core field is therefore constructed.  The only
remaining input to the moving-core atomic compiler is stationary mass
tightness outside the selected positive source core.

## Axiom gate

Only finite carrier searches, executable cutoff moduli, and exact rational
order/algebra are used.  There is no classical choice, noncomputable
declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffConditionalCoreCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffConditionalCoreModulus

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffConditionalCoreCauchy
open YMGap.Continuum.BF4PhysicalCutoffConditionalCoreReduction
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffPositiveRowPersistence
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalHSCauchy
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
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

/-! ## 1. Noncircular source-floor and target-tail budgets -/

def centralPhysicalConditioningQuotientBudget
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') : Q' :=
  (HalfPow.half * epsilon) *
    centralPhysicalMovingPositiveRowFloor w hw sourceBase half

def centralPhysicalConditioningOldTolerance
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half *
    centralPhysicalConditioningQuotientBudget
      w hw sourceBase half epsilon)

def centralPhysicalConditioningShellTolerance
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') : Q' :=
  HalfPow.half * centralPhysicalConditioningOldTolerance
    w hw sourceBase half epsilon

def centralPhysicalConditioningTargetBase
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') : Nat :=
  max sourceBase
    (centralPhysicalTargetShellCutoff w half
      (centralPhysicalConditioningShellTolerance
        w hw sourceBase half epsilon))

def centralPhysicalConditioningActionRate
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') : Nat :=
  centralOldCarrierHSCutoff w
    (centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon)
    half
    (centralPhysicalConditioningOldTolerance
      w hw sourceBase half epsilon)

theorem centralPhysicalConditioningQuotientBudget_pos
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < centralPhysicalConditioningQuotientBudget
      w hw sourceBase half epsilon := by
  unfold centralPhysicalConditioningQuotientBudget
  exact Q'.mul_pos
    (ExpNeg.half_mul_pos epsilon hepsilon)
    (centralPhysicalMovingPositiveRowFloor_pos
      w hw sourceBase half)

theorem centralPhysicalConditioningOldTolerance_pos
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < centralPhysicalConditioningOldTolerance
      w hw sourceBase half epsilon := by
  unfold centralPhysicalConditioningOldTolerance
  exact ExpNeg.half_mul_pos _
    (ExpNeg.half_mul_pos _
      (centralPhysicalConditioningQuotientBudget_pos
        w hw sourceBase half hepsilon))

theorem centralPhysicalConditioningShellTolerance_pos
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < centralPhysicalConditioningShellTolerance
      w hw sourceBase half epsilon := by
  unfold centralPhysicalConditioningShellTolerance
  exact ExpNeg.half_mul_pos _
    (centralPhysicalConditioningOldTolerance_pos
      w hw sourceBase half hepsilon)

theorem sourceBase_le_centralPhysicalConditioningTargetBase
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') :
    sourceBase <= centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon := by
  unfold centralPhysicalConditioningTargetBase
  exact Nat.le_max_left _ _

theorem targetShellCutoff_le_centralPhysicalConditioningTargetBase
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') :
    centralPhysicalTargetShellCutoff w half
        (centralPhysicalConditioningShellTolerance
          w hw sourceBase half epsilon) <=
      centralPhysicalConditioningTargetBase
        w hw sourceBase half epsilon := by
  unfold centralPhysicalConditioningTargetBase
  exact Nat.le_max_right _ _

theorem targetBase_le_centralPhysicalConditioningActionRate
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') :
    centralPhysicalConditioningTargetBase
        w hw sourceBase half epsilon <=
      centralPhysicalConditioningActionRate
        w hw sourceBase half epsilon := by
  unfold centralPhysicalConditioningActionRate
    centralOldCarrierHSCutoff
  exact Nat.le_max_left _ _

theorem sourceBase_le_centralPhysicalConditioningActionRate
    (w : Q') (hw : (0 : Q') <= w)
    (sourceBase half : Nat) (epsilon : Q') :
    sourceBase <= centralPhysicalConditioningActionRate
      w hw sourceBase half epsilon :=
  Nat.le_trans
    (sourceBase_le_centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon)
    (targetBase_le_centralPhysicalConditioningActionRate
      w hw sourceBase half epsilon)

/-! ## 2. The three scheduled finite errors -/

theorem centralPhysicalConditioningOldL1_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half sourceBase : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second : Nat}
    (hfirst : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= first)
    (hsecond : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= second)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0) sourceBase half) :
    centralOldRowCutoffDifferenceL1
        w (Q'.le_of_lt hw0)
        (centralPhysicalConditioningTargetBase
          w (Q'.le_of_lt hw0) sourceBase half epsilon)
        first second half source <=
      centralPhysicalConditioningOldTolerance
        w (Q'.le_of_lt hw0) sourceBase half epsilon := by
  let hw := Q'.le_of_lt hw0
  let targetBase := centralPhysicalConditioningTargetBase
    w hw sourceBase half epsilon
  let oldTolerance := centralPhysicalConditioningOldTolerance
    w hw sourceBase half epsilon
  have hsourceTarget := mem_centralPositiveHalfStates_of_le
    hw
    (sourceBase_le_centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon)
    hsource
  have htargetParts := mem_centralPositiveHalfStates_iff.mp hsourceTarget
  have holdPos : (0 : Q') < oldTolerance := by
    unfold oldTolerance hw
    exact centralPhysicalConditioningOldTolerance_pos
      w (Q'.le_of_lt hw0) sourceBase half hepsilon
  exact centralOldRowCutoffDifferenceL1_le
    hw0 hw1 targetBase half holdPos hfirst hsecond source htargetParts.1

theorem centralPhysicalConditioningTargetShell_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half sourceBase : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {later : Nat}
    (hlater : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= later)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0) sourceBase half) :
    centralOldRowJointTargetShellMass
        w (Q'.le_of_lt hw0)
        (centralPhysicalConditioningTargetBase
          w (Q'.le_of_lt hw0) sourceBase half epsilon)
        later half source <=
      centralPhysicalConditioningShellTolerance
        w (Q'.le_of_lt hw0) sourceBase half epsilon := by
  let hw := Q'.le_of_lt hw0
  let targetBase := centralPhysicalConditioningTargetBase
    w hw sourceBase half epsilon
  let shellTolerance := centralPhysicalConditioningShellTolerance
    w hw sourceBase half epsilon
  have hbaseTarget : sourceBase <= targetBase :=
    sourceBase_le_centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon
  have htargetAction : targetBase <=
      centralPhysicalConditioningActionRate
        w hw sourceBase half epsilon :=
    targetBase_le_centralPhysicalConditioningActionRate
      w hw sourceBase half epsilon
  have htargetLater : targetBase <= later :=
    Nat.le_trans htargetAction hlater
  have hsourceTarget := mem_centralPositiveHalfStates_of_le
    hw hbaseTarget hsource
  have htargetParts := mem_centralPositiveHalfStates_iff.mp hsourceTarget
  have hshellPos : (0 : Q') < shellTolerance := by
    unfold shellTolerance hw
    exact centralPhysicalConditioningShellTolerance_pos
      w (Q'.le_of_lt hw0) sourceBase half hepsilon
  exact centralOldRowJointTargetShellMass_le_of_scheduled_base
    hw0 hw1 half hshellPos
    (targetShellCutoff_le_centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon)
    htargetLater htargetParts.1

/-! ## 3. Exact budget contraction through the quotient -/

theorem centralPhysicalConditioningCoreError_double_le_budget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half sourceBase : Nat)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second : Nat}
    (hfirst : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= first)
    (hsecond : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= second)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0) sourceBase half) :
    let error := centralPhysicalConditioningCoreError
      w (Q'.le_of_lt hw0)
      (centralPhysicalConditioningTargetBase
        w (Q'.le_of_lt hw0) sourceBase half epsilon)
      first second half source
    error + error <= centralPhysicalConditioningQuotientBudget
      w (Q'.le_of_lt hw0) sourceBase half epsilon := by
  dsimp only
  let hw := Q'.le_of_lt hw0
  let budget := centralPhysicalConditioningQuotientBudget
    w hw sourceBase half epsilon
  let oldTolerance := centralPhysicalConditioningOldTolerance
    w hw sourceBase half epsilon
  let shellTolerance := centralPhysicalConditioningShellTolerance
    w hw sourceBase half epsilon
  let targetBase := centralPhysicalConditioningTargetBase
    w hw sourceBase half epsilon
  let error := centralPhysicalConditioningCoreError
    w hw targetBase first second half source
  have hold := centralPhysicalConditioningOldL1_le
    hw0 hw1 half sourceBase hepsilon hfirst hsecond hsource
  have hfirstShell := centralPhysicalConditioningTargetShell_le
    hw0 hw1 half sourceBase hepsilon hfirst hsource
  have hsecondShell := centralPhysicalConditioningTargetShell_le
    hw0 hw1 half sourceBase hepsilon hsecond hsource
  have herror : error <= oldTolerance +
      (shellTolerance + shellTolerance) := by
    unfold error centralPhysicalConditioningCoreError
    exact Q'.add_le_add hold
      (Q'.add_le_add hfirstShell hsecondShell)
  have hshellPair : shellTolerance + shellTolerance ≈ oldTolerance := by
    unfold shellTolerance
    exact ExpNeg.two_halves oldTolerance
  have hhalfBudget : oldTolerance + oldTolerance ≈
      HalfPow.half * budget := by
    unfold oldTolerance
    exact ExpNeg.two_halves (HalfPow.half * budget)
  have herrorHalf : error <= HalfPow.half * budget := by
    refine Q'.le_trans' _ _ _ herror ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ (oldTolerance + oldTolerance) _
        (Q'.add_eqv_congr_left oldTolerance _ _ hshellPair)
        hhalfBudget)
  have hdouble := Q'.add_le_add herrorHalf herrorHalf
  exact Q'.le_trans' _ _ _ hdouble
    (Q'.le_of_eqv (ExpNeg.two_halves budget))

private theorem divPos_mul_right_eqv_local
    (value floor : Q') (hfloor : (0 : Q') < floor) :
    Q'.divPos (value * floor) floor hfloor ≈ value := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (value * (floor * Q'.recipPos floor hfloor)) _
    (Q'.mul_assoc_eqv value floor
      (Q'.recipPos floor hfloor)) ?_
  refine Q'.eqv_trans _ (value * 1) _
    (Q'.mul_eqv_congr_left value _ _
      (Q'.mul_recipPos_eqv floor hfloor)) ?_
  exact Q'.mul_one_eqv value

theorem centralPhysicalMarkovApply_abs_sub_le_half_epsilon
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half sourceBase : Nat)
    (hretained :
      centralPhysicalUniformRowFloorCutoff w half <= sourceBase)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second : Nat}
    (hfirst : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= first)
    (hsecond : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= second)
    (observable : CentralPhysicalUnitObservable)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0) sourceBase half) :
    Q'.abs
        (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) first half observable.value source +
          -centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) second half observable.value source) <=
      HalfPow.half * epsilon := by
  let hw := Q'.le_of_lt hw0
  let targetBase := centralPhysicalConditioningTargetBase
    w hw sourceBase half epsilon
  let actionRate := centralPhysicalConditioningActionRate
    w hw sourceBase half epsilon
  let error := centralPhysicalConditioningCoreError
    w hw targetBase first second half source
  let floor := centralPhysicalMovingPositiveRowFloor
    w hw sourceBase half
  let budget := centralPhysicalConditioningQuotientBudget
    w hw sourceBase half epsilon
  have hsourceTarget : sourceBase <= targetBase :=
    sourceBase_le_centralPhysicalConditioningTargetBase
      w hw sourceBase half epsilon
  have htargetAction : targetBase <= actionRate := by
    unfold actionRate
    exact targetBase_le_centralPhysicalConditioningActionRate
      w hw sourceBase half epsilon
  have htargetFirst : targetBase <= first :=
    Nat.le_trans htargetAction hfirst
  have htargetSecond : targetBase <= second :=
    Nat.le_trans htargetAction hsecond
  have hpoint :=
    centralPhysicalMarkovApply_abs_sub_le_conditioningCoreError
      hw0 hw1 half hretained hsourceTarget
      htargetFirst htargetSecond observable hsource
  have herror : error + error <= budget := by
    unfold error budget targetBase hw
    exact centralPhysicalConditioningCoreError_double_le_budget
      hw0 hw1 half sourceBase hepsilon hfirst hsecond hsource
  have hfloorPos : (0 : Q') < floor := by
    unfold floor
    exact centralPhysicalMovingPositiveRowFloor_pos
      w hw sourceBase half
  have hquotient : Q'.divPos (error + error) floor hfloorPos <=
      Q'.divPos budget floor hfloorPos := by
    unfold Q'.divPos
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ herror
      (Q'.le_of_lt (Q'.recipPos_pos floor hfloorPos))
  have hcancel : Q'.divPos budget floor hfloorPos ≈
      HalfPow.half * epsilon := by
    unfold budget centralPhysicalConditioningQuotientBudget floor
    exact divPos_mul_right_eqv_local _ _ _
  exact Q'.le_trans' _ _ _ hpoint
    (Q'.le_trans' _ _ _ hquotient (Q'.le_of_eqv hcancel))

/-! ## 4. Squared core estimate for the recoded unit observables -/

private theorem unitObservable_sub_sq_le_abs
    (left right : CentralPhysicalUnitObservable)
    (state : EdgeLabelling) :
    let difference := left.value state + -(right.value state)
    difference * difference <= Q'.abs difference := by
  dsimp only
  let difference := left.value state + -(right.value state)
  have honeLeRightAdd : (1 : Q') <= right.value state + 1 := by
    have h := Q'.add_le_add_right
      (0 : Q') (right.value state) 1 (right.nonnegative state)
    rwa [Q'.zero_add'] at h
  have honeLeLeftAdd : (1 : Q') <= left.value state + 1 := by
    have h := Q'.add_le_add_right
      (0 : Q') (left.value state) 1 (left.nonnegative state)
    rwa [Q'.zero_add'] at h
  have hforward : left.value state <= right.value state + 1 :=
    Q'.le_trans' _ _ _ (left.le_one state) honeLeRightAdd
  have hbackward : right.value state <= left.value state + 1 :=
    Q'.le_trans' _ _ _ (right.le_one state) honeLeLeftAdd
  have habs : Q'.abs difference <= (1 : Q') :=
    CReal.abs_sub_le_of_bounds hforward hbackward
  have hsquareAbs : difference * difference <=
      Q'.abs difference * Q'.abs difference :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (ExpNeg.abs_mul_le difference difference)
  have habsProduct : Q'.abs difference * Q'.abs difference <=
      (1 : Q') * Q'.abs difference :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ habs
      (Q'.abs_nonneg difference)
  exact Q'.le_trans' _ _ _ hsquareAbs
    (Q'.le_trans' _ _ _ habsProduct
      (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs difference))))

theorem centralPhysicalMarkovCutoffUnitObservable_coreSq_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half sourceBase : Nat)
    (hretained :
      centralPhysicalUniformRowFloorCutoff w half <= sourceBase)
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {first second : Nat}
    (hfirst : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= first)
    (hsecond : centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) sourceBase half epsilon <= second)
    (observable : CentralPhysicalUnitObservable)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0) sourceBase half) :
    let left := centralPhysicalMarkovCutoffUnitObservable
      (Q'.le_of_lt hw0) first half observable
    let right := centralPhysicalMarkovCutoffUnitObservable
      (Q'.le_of_lt hw0) second half observable
    let difference := left.value source + -(right.value source)
    difference * difference <= HalfPow.half * epsilon := by
  dsimp only
  let hw := Q'.le_of_lt hw0
  let left := centralPhysicalMarkovCutoffUnitObservable
    hw first half observable
  let right := centralPhysicalMarkovCutoffUnitObservable
    hw second half observable
  let difference := left.value source + -(right.value source)
  have hsourceFirstCutoff : sourceBase <= first :=
    Nat.le_trans
      (sourceBase_le_centralPhysicalConditioningActionRate
        w hw sourceBase half epsilon) hfirst
  have hsourceSecondCutoff : sourceBase <= second :=
    Nat.le_trans
      (sourceBase_le_centralPhysicalConditioningActionRate
        w hw sourceBase half epsilon) hsecond
  have hsourceFirst := mem_centralPositiveHalfStates_of_le
    hw hsourceFirstCutoff hsource
  have hsourceSecond := mem_centralPositiveHalfStates_of_le
    hw hsourceSecondCutoff hsource
  have hvalueFirst :=
    centralPhysicalMarkovCutoffUnitObservable_value_of_mem
      hw first half observable source hsourceFirst
  have hvalueSecond :=
    centralPhysicalMarkovCutoffUnitObservable_value_of_mem
      hw second half observable source hsourceSecond
  have hmarkovAbs := centralPhysicalMarkovApply_abs_sub_le_half_epsilon
    hw0 hw1 half sourceBase hretained hepsilon
    hfirst hsecond observable hsource
  have hinside : difference ≈
      centralPhysicalMarkovApply
          w hw first half observable.value source +
        -centralPhysicalMarkovApply
          w hw second half observable.value source :=
    Q'.add_eqv_congr' hvalueFirst
      (Q'.neg_eqv_congr _ _ hvalueSecond)
  have habs : Q'.abs difference <= HalfPow.half * epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hinside)) hmarkovAbs
  exact Q'.le_trans' _ _ _
    (unitObservable_sub_sq_le_abs left right source) habs

/-! ## 5. Contracting the residual to stationary source-shell tightness -/

/-- The sole remaining analytic input for atomic Markov Cauchyness: an
accuracy-dependent positive source core, beyond the unit-tail cutoff, whose
stationary complementary mass is eventually small. -/
structure CentralPhysicalStationaryPositiveSourceTailData
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat) : Type where
  base : CentralPhysicalUnitObservable -> Q' -> Nat
  uniformFloorCutoff_le_base : forall observable epsilon,
    centralPhysicalUniformRowFloorCutoff w half <= base observable epsilon
  stageRate : CentralPhysicalUnitObservable -> Q' -> Nat
  shellMass : forall
    (observable : CentralPhysicalUnitObservable)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall cutoff, stageRate observable epsilon <= cutoff ->
      centralPhysicalRowMarginalOutsideBase
        w (Q'.le_of_lt hw0) cutoff half (base observable epsilon) <=
          HalfPow.half * epsilon

/-- Stationary positive-source tail tightness now constructs every field of
the existing moving-core atomic Cauchy datum; the conditional core is supplied
by the executable modulus above. -/
def CentralPhysicalStationaryPositiveSourceTailData.toCoreTailCauchyData
    {w : Q'} {hw0 : (0 : Q') < w}
    {hw1 : w < (1 : Q')} {half : Nat}
    (data : CentralPhysicalStationaryPositiveSourceTailData hw0 hw1 half) :
    CentralPhysicalAtomicMarkovCoreTailCauchyData hw0 hw1 half where
  base := data.base
  actionRate := fun observable epsilon =>
    centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) (data.base observable epsilon) half epsilon
  base_le_actionRate := by
    intro observable epsilon
    exact sourceBase_le_centralPhysicalConditioningActionRate
      w (Q'.le_of_lt hw0) (data.base observable epsilon) half epsilon
  stageRate := data.stageRate
  coreSq := by
    intro observable epsilon hepsilon first second hfirst hsecond
      state hsupport hwithin hpositive
    have hcarrier : state ∈ centralHalfStates
        (data.base observable epsilon) half := by
      unfold centralHalfStates
      apply boundedEdgeLabellings_complete
      · exact (labelWithinB_true_iff
          (data.base observable epsilon)
          (centralLowerFaceIds half) state).mp hwithin
      · exact hsupport
    have hsource : state ∈ centralPositiveHalfStates
        w (Q'.le_of_lt hw0) (data.base observable epsilon) half :=
      mem_centralPositiveHalfStates_iff.mpr ⟨hcarrier, hpositive⟩
    exact centralPhysicalMarkovCutoffUnitObservable_coreSq_le
      hw0 hw1 half (data.base observable epsilon)
      (data.uniformFloorCutoff_le_base observable epsilon)
      hepsilon hfirst hsecond observable hsource
  shellMass := data.shellMass

def CentralPhysicalStationaryPositiveSourceTailData.toAtomicCauchyData
    {w : Q'} {hw0 : (0 : Q') < w}
    {hw1 : w < (1 : Q')} {half : Nat}
    (data : CentralPhysicalStationaryPositiveSourceTailData hw0 hw1 half) :=
  data.toCoreTailCauchyData.toAtomicCauchyData

def CentralPhysicalStationaryPositiveSourceTailData.toDenseCauchyData
    {w : Q'} {hw0 : (0 : Q') < w}
    {hw1 : w < (1 : Q')} {half : Nat}
    (data : CentralPhysicalStationaryPositiveSourceTailData hw0 hw1 half) :=
  data.toCoreTailCauchyData.toDenseCauchyData

/-! ## Axiom audit -/

#print axioms centralPhysicalConditioningActionRate
#print axioms centralPhysicalConditioningCoreError_double_le_budget
#print axioms centralPhysicalMarkovApply_abs_sub_le_half_epsilon
#print axioms centralPhysicalMarkovCutoffUnitObservable_coreSq_le
#print axioms CentralPhysicalStationaryPositiveSourceTailData
#print axioms CentralPhysicalStationaryPositiveSourceTailData.toCoreTailCauchyData
#print axioms CentralPhysicalStationaryPositiveSourceTailData.toAtomicCauchyData
#print axioms CentralPhysicalStationaryPositiveSourceTailData.toDenseCauchyData

end YMGap.Continuum.BF4PhysicalCutoffConditionalCoreModulus
