/-
# A uniform later-cutoff floor for positive physical BF4 rows

Qualitative row positivity is insufficient for uniform conditioning: the
inverse marginal must be bounded on the fixed old positive carrier.  This
file constructs such a bound without a circular convergence schedule.

Anchor the representation cutoff at the existing degree-thirteen retained
cutoff for complete new-label tolerance `1`.  A source-cylinder numerator is
retained exactly and only gains nonnegative new-label mass.  The partition
also splits exactly, and its increment is at most `1`; because the anchor
partition is at least `1`, the later partition is at most twice the anchor
partition.  Exact rational cross multiplication then proves that every later
source marginal is at least half its anchor value.

Taking half of the already constructed finite minimum over positive anchor
rows therefore gives one explicit positive floor, uniform in every later
representation cutoff.

## Axiom gate

Only finite-list recoding and exact rational inequalities are used.  There is
no classical choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffTargetShellTail

namespace YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4ReflectedAllSpinTaylorRankOneEndpoint
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The aggregate source cylinder -/

def centralSourceCylinderB
    (half : Nat) (source physical : EdgeLabelling) : Bool :=
  labellingsAgreeOnB
    (centralLowerFaceIds half)
    (centralLowerRestriction half physical) source

def centralSourceCylinderIndicator
    (half : Nat) (source physical : EdgeLabelling) : Q' :=
  if centralSourceCylinderB half source physical then 1 else 0

def centralSourceCylinderObservable
    (half : Nat) (source : EdgeLabelling) :
    CutoffStableSlabUnitObservable (centralExtent half) where
  value := fun _cutoff physical =>
    centralSourceCylinderIndicator half source physical
  nonnegative := by
    intro _cutoff physical _
    unfold centralSourceCylinderIndicator
    cases centralSourceCylinderB half source physical <;> decide
  le_one := by
    intro _cutoff physical _
    unfold centralSourceCylinderIndicator
    cases centralSourceCylinderB half source physical <;> decide
  cutoff_stable := by
    intro _K _L _physical _ _
    exact Q'.eqv_refl _

private theorem centralSourceCylinderIndicator_assembled
    {K half : Nat}
    {source left right boundary : EdgeLabelling}
    (hleft : left ∈ centralHalfStates K half) :
    centralSourceCylinderIndicator half source
        (assembleReflectedSlabLabelling
          half left boundary right) =
      if labellingsAgreeOnB
          (centralLowerFaceIds half) left source
      then 1 else 0 := by
  unfold centralSourceCylinderIndicator centralSourceCylinderB
  rw [centralLowerRestriction_assemble hleft]

private theorem assembledSourceCylinderNumerator_eq_rawRow
    {w : Q'} {K half : Nat} {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    listQSum
        (fun physical =>
          centralSourceCylinderIndicator half source physical *
            slabParametricKPhysicalTerm
              w K (centralExtent half) physical)
        (centralAssembledSlabLabellings K half) ≈
      listQSum
        (centralPhysicalReflectedKernel w K half source)
        (centralHalfStates K half) := by
  let leftPredicate : EdgeLabelling -> Bool :=
    fun left => labellingsAgreeOnB
      (centralLowerFaceIds half) left source
  let rightPredicate : EdgeLabelling -> Bool := fun _ => true
  let term : EdgeLabelling -> EdgeLabelling ->
      EdgeLabelling -> Q' :=
    fun left right boundary =>
      slabParametricKPhysicalTerm
        w K (centralExtent half)
        (assembleReflectedSlabLabelling
          half left boundary right)
  unfold centralAssembledSlabLabellings
  rw [listQSum_map]
  refine Q'.eqv_trans _
    (listQSum
      (fun triple =>
        if leftPredicate triple.1 &&
            rightPredicate triple.2.1
        then term triple.1 triple.2.1 triple.2.2
        else 0)
      (centralReflectionTriples K half)) _ ?_ ?_
  · apply listQSum_congr_on
    intro triple htriple
    have hparts := mem_centralReflectionTriples.mp htriple
    unfold assembleCentralReflectionTriple
    rw [centralSourceCylinderIndicator_assembled hparts.1]
    dsimp only [leftPredicate, rightPredicate, term]
    simp only [Bool.and_true]
    cases hselected :
        labellingsAgreeOnB
          (centralLowerFaceIds half) triple.1 source
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.zero_mul_eqv _
    · simp only [if_true]
      exact Q'.one_mul_eqv _
  · unfold centralReflectionTriples
    have hselector :=
      listQSum_left_selector_right_filter
        (centralHalfStates K half)
        (centralHalfStates K half)
        (centralBoundaryChannels K half)
        leftPredicate rightPredicate term source
        (centralHalfStates_nodup K half)
        hsource
        (labellingsAgreeOnB_self
          (centralLowerFaceIds half) source)
        (fun left hleft hagree =>
          eq_of_labellingsAgreeOnB_of_bounded
            hleft hsource hagree)
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          listQSum (term source right)
            (centralBoundaryChannels K half))
        ((centralHalfStates K half).filter rightPredicate)) _
      hselector ?_
    have hfilter :
        (centralHalfStates K half).filter rightPredicate =
          centralHalfStates K half := by
      apply List.filter_eq_self.mpr
      intro _ _
      rfl
    rw [hfilter]
    unfold term centralPhysicalReflectedKernel
    exact Q'.eqv_refl _

theorem centralSourceCylinderNumerator_eq_rawRow
    {w : Q'} {K half : Nat} {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    slabBoundedObservableNumerator
        w K (centralExtent half)
        (centralSourceCylinderObservable half source) ≈
      listQSum
        (centralPhysicalReflectedKernel w K half source)
        (centralHalfStates K half) := by
  unfold slabBoundedObservableNumerator
    centralSourceCylinderObservable
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_centralAssembledSlabLabellings
        (fun physical =>
          centralSourceCylinderIndicator half source physical *
            slabParametricKPhysicalTerm
              w K (centralExtent half) physical)
        K half))
    (assembledSourceCylinderNumerator_eq_rawRow hsource)

/-- A physical source-row marginal is exactly the normalized expectation of
its aggregate lower source cylinder. -/
theorem centralPhysicalRowMarginal_eq_sourceExpectation
    {w : Q'} (hw : (0 : Q') <= w)
    {K half : Nat} {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates K half) :
    centralPhysicalRowMarginal w hw K half source ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw K (centralExtent half)
        (centralSourceCylinderObservable half source) := by
  have hpartition :
      (0 : Q') < slabParametricKPhysicalPartition
        w K (centralExtent half) :=
    slabParametricKPhysicalPartition_pos
      hw K (centralExtent half)
  have hnumerator :=
    centralSourceCylinderNumerator_eq_rawRow
      (w := w) hsource
  unfold centralPhysicalRowMarginal
    centralNormalizedPhysicalReflectedKernel
    slabNomeCutoffBoundedObservableExpectation Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
        (centralPhysicalReflectedKernel w K half source)
        (centralHalfStates K half) *
      Q'.recipPos
        (slabParametricKPhysicalPartition
          w K (centralExtent half)) hpartition) _
    (listQSum_mul_right
      (centralPhysicalReflectedKernel w K half source)
      (Q'.recipPos
        (slabParametricKPhysicalPartition
          w K (centralExtent half)) hpartition)
      (centralHalfStates K half)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm hnumerator)

/-! ## 2. Exact rational half-retention algebra -/

private theorem divPos_half_le_of_retained_numerator_and_unit_increment
    (anchorNumerator laterNumerator anchorPartition laterPartition
      increment : Q')
    (hanchorNumerator0 : (0 : Q') <= anchorNumerator)
    (hanchorNumeratorLater : anchorNumerator <= laterNumerator)
    (hanchorPartition : (0 : Q') < anchorPartition)
    (hlaterPartition : (0 : Q') < laterPartition)
    (hanchorPartitionOne : (1 : Q') <= anchorPartition)
    (hincrementOne : increment <= (1 : Q'))
    (hlaterDecomposition :
      laterPartition ≈ anchorPartition + increment) :
    HalfPow.half *
        Q'.divPos anchorNumerator anchorPartition hanchorPartition <=
      Q'.divPos laterNumerator laterPartition hlaterPartition := by
  let coefficient := HalfPow.half *
    Q'.divPos anchorNumerator anchorPartition hanchorPartition
  have hquotient0 :
      (0 : Q') <=
        Q'.divPos anchorNumerator anchorPartition hanchorPartition := by
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _ hanchorNumerator0
      (Q'.le_of_lt
        (Q'.recipPos_pos anchorPartition hanchorPartition))
  have hcoefficient0 : (0 : Q') <= coefficient :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg hquotient0
  have hincrementAnchor : increment <= anchorPartition :=
    Q'.le_trans' _ _ _ hincrementOne hanchorPartitionOne
  have hlaterLeDouble :
      laterPartition <= anchorPartition + anchorPartition := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv hlaterDecomposition) ?_
    exact Q'.add_le_add_left
      anchorPartition increment anchorPartition
      hincrementAnchor
  have hcoefficientStep :
      coefficient * laterPartition <=
        coefficient * (anchorPartition + anchorPartition) :=
    Q'.mul_le_mul_of_nonneg_left
      laterPartition
      (anchorPartition + anchorPartition)
      coefficient hlaterLeDouble hcoefficient0
  have hcoefficientAnchor :
      coefficient * anchorPartition ≈
        HalfPow.half * anchorNumerator := by
    unfold coefficient
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv HalfPow.half
        (Q'.divPos anchorNumerator
          anchorPartition hanchorPartition)
        anchorPartition)
      (Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.divPos_mul_eqv anchorNumerator
          anchorPartition hanchorPartition))
  have hcollapse :
      coefficient * (anchorPartition + anchorPartition) ≈
        anchorNumerator := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv coefficient
        anchorPartition anchorPartition)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          hcoefficientAnchor hcoefficientAnchor)
        (ExpNeg.two_halves anchorNumerator))
  apply Q'.le_divPos_of_mul_le
  exact Q'.le_trans' _ _ _ hcoefficientStep
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hcollapse)
      hanchorNumeratorLater)

/-- If the complete new-label increment is at most one, every carried source
row at the later cutoff retains at least half of its anchor marginal. -/
theorem half_mul_centralPhysicalRowMarginal_le_of_increment_le_one
    {w : Q'} (hw : (0 : Q') <= w)
    {anchor later half : Nat} (hcutoff : anchor <= later)
    (hincrementOne :
      slabParametricKCutoffIncrement
        w anchor later (centralExtent half) <= (1 : Q'))
    {source : EdgeLabelling}
    (hsource : source ∈ centralHalfStates anchor half) :
    HalfPow.half *
        centralPhysicalRowMarginal w hw anchor half source <=
      centralPhysicalRowMarginal w hw later half source := by
  have hsourceLater : source ∈ centralHalfStates later half := by
    unfold centralHalfStates at hsource ⊢
    have hsound := boundedEdgeLabellings_sound
      anchor (centralLowerFaceIds half) source hsource
    apply boundedEdgeLabellings_complete
    · intro edge hedge
      have hbound := hsound.1 edge hedge
      omega
    · exact hsound.2
  let observable := centralSourceCylinderObservable half source
  let anchorNumerator := slabBoundedObservableNumerator
    w anchor (centralExtent half) observable
  let laterNumerator := slabBoundedObservableNumerator
    w later (centralExtent half) observable
  let anchorPartition := slabParametricKPhysicalPartition
    w anchor (centralExtent half)
  let laterPartition := slabParametricKPhysicalPartition
    w later (centralExtent half)
  let increment := slabParametricKCutoffIncrement
    w anchor later (centralExtent half)
  have hanchorNumerator0 : (0 : Q') <= anchorNumerator := by
    dsimp only [anchorNumerator]
    exact slabBoundedObservableNumerator_nonnegative
      hw anchor (centralExtent half) observable
  have hobservableIncrement0 :
      (0 : Q') <= slabBoundedObservableCutoffIncrement
        w anchor later (centralExtent half) observable :=
    slabBoundedObservableCutoffIncrement_nonnegative
      hw anchor later (centralExtent half) observable
  have hnumeratorDecomposition :=
    slabBoundedObservableNumerator_eq_base_add_increment
      (w := w) hcutoff observable
  have hanchorNumeratorLater :
      anchorNumerator <= laterNumerator := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ hobservableIncrement0) ?_
    exact Q'.ge_of_eqv hnumeratorDecomposition
  have hanchorPartitionPos : (0 : Q') < anchorPartition := by
    dsimp only [anchorPartition]
    exact slabParametricKPhysicalPartition_pos
      hw anchor (centralExtent half)
  have hlaterPartitionPos : (0 : Q') < laterPartition := by
    dsimp only [laterPartition]
    exact slabParametricKPhysicalPartition_pos
      hw later (centralExtent half)
  have hanchorPartitionOne : (1 : Q') <= anchorPartition := by
    dsimp only [anchorPartition]
    exact slabParametricKPhysicalPartition_one_le
      hw anchor (centralExtent half)
  have hpartitionDecomposition :=
    slabParametricKPhysicalPartition_eq_base_add_increment
      (w := w) (extent := centralExtent half) hcutoff
  have hratio :
      HalfPow.half *
          Q'.divPos anchorNumerator anchorPartition
            hanchorPartitionPos <=
        Q'.divPos laterNumerator laterPartition
          hlaterPartitionPos :=
    divPos_half_le_of_retained_numerator_and_unit_increment
      anchorNumerator laterNumerator anchorPartition laterPartition
      increment hanchorNumerator0 hanchorNumeratorLater
      hanchorPartitionPos hlaterPartitionPos hanchorPartitionOne
      hincrementOne hpartitionDecomposition
  have hanchorEq :=
    centralPhysicalRowMarginal_eq_sourceExpectation
      (K := anchor) (half := half) (source := source) hw hsource
  have hlaterEq :=
    centralPhysicalRowMarginal_eq_sourceExpectation
      (K := later) (half := half) (source := source) hw hsourceLater
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left HalfPow.half _ _ hanchorEq)) ?_
  refine Q'.le_trans' _ _ _ hratio ?_
  exact Q'.ge_of_eqv hlaterEq

/-! ## 3. The explicit uniform positive-row floor -/

def centralPhysicalUniformRowFloorCutoff
    (w : Q') (half : Nat) : Nat :=
  centralPhysicalTargetShellCutoff w half 1

def centralPhysicalUniformPositiveRowFloor
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) : Q' :=
  HalfPow.half *
    (centralPositivePhysicalMarginalFloorData
      w hw (centralPhysicalUniformRowFloorCutoff w half) half).floor

theorem centralPhysicalUniformPositiveRowFloor_pos
    (w : Q') (hw : (0 : Q') <= w) (half : Nat) :
    (0 : Q') <
      centralPhysicalUniformPositiveRowFloor w hw half := by
  unfold centralPhysicalUniformPositiveRowFloor
  exact ExpNeg.half_mul_pos _
    (centralPositivePhysicalMarginalFloorData
      w hw (centralPhysicalUniformRowFloorCutoff w half) half).floor_pos

/-- One positive rational floor works for every anchor-positive source and
every later representation cutoff. -/
theorem centralPhysicalUniformPositiveRowFloor_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (half : Nat)
    {later : Nat}
    (hlater : centralPhysicalUniformRowFloorCutoff w half <= later)
    {source : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates
      w (Q'.le_of_lt hw0)
      (centralPhysicalUniformRowFloorCutoff w half) half) :
    centralPhysicalUniformPositiveRowFloor
        w (Q'.le_of_lt hw0) half <=
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw0) later half source := by
  have hparts := mem_centralPositiveHalfStates_iff.mp hsource
  have hanchorFloor :=
    (centralPositivePhysicalMarginalFloorData
      w (Q'.le_of_lt hw0)
      (centralPhysicalUniformRowFloorCutoff w half) half).floor_le
      source hsource
  have hhalfFloor :
      centralPhysicalUniformPositiveRowFloor
          w (Q'.le_of_lt hw0) half <=
        HalfPow.half *
          centralPhysicalRowMarginal
            w (Q'.le_of_lt hw0)
            (centralPhysicalUniformRowFloorCutoff w half) half source := by
    unfold centralPhysicalUniformPositiveRowFloor
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      hanchorFloor HalfPow.half_nonneg
  have hincrement :
      slabParametricKCutoffIncrement
          w (centralPhysicalUniformRowFloorCutoff w half)
          later (centralExtent half) <= (1 : Q') := by
    unfold centralPhysicalUniformRowFloorCutoff
      centralPhysicalTargetShellCutoff
    exact slabPhysicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 (centralExtent half) (by decide) hlater
  exact Q'.le_trans' _ _ _ hhalfFloor
    (half_mul_centralPhysicalRowMarginal_le_of_increment_le_one
      (Q'.le_of_lt hw0) hlater hincrement hparts.1)

/-! ## Axiom audit -/

#print axioms centralSourceCylinderObservable
#print axioms centralSourceCylinderNumerator_eq_rawRow
#print axioms centralPhysicalRowMarginal_eq_sourceExpectation
#print axioms half_mul_centralPhysicalRowMarginal_le_of_increment_le_one
#print axioms centralPhysicalUniformRowFloorCutoff
#print axioms centralPhysicalUniformPositiveRowFloor
#print axioms centralPhysicalUniformPositiveRowFloor_le

end YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
