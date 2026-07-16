/-
# Centered constructive-real closure of half-time reflection positivity

A finite positive-time cylinder polynomial uses finitely many centered
cylinder events.  Each pair event already has an unconditional constructive
real in the derived strong-coupling window, with the literal centered volume
and spin-cutoff schedules.  This file assembles their signed finite quadratic
as a `CReal`.

The half-time corrected-slab argument supplies stagewise lower bounds for a
support-coordinate presentation of that quadratic.  Two exact finite chart
obligations remain visible:

* pair events in the half-time ambient chart agree with the corresponding
  centered receding events;
* the finite coefficient list is the zero-extended/reindexed support
  coefficient in the half-time chart.

Given those identities, a carrier-floor schedule whose explicit quadratic
modulus tends to zero proves sound reflection positivity of the centered
constructive real.  The final order lemma is the vanishing-error companion to
`FiniteWeightedGramCRealLimit`'s exact-nonnegative bridge.
-/

import YMGap.Continuum.FiniteWeightedGramCRealLimit
import YMGap.Continuum.Z4HalfTimeReflectionAmbientQuadraticStability
import YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.FiniteWeightedGramCRealLimit
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionAmbientQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite family of centered joint cylinders -/

/-- Exact finite data for a centered joint cylinder polynomial.  Different
matrix entries may use different finite root charts, but every chart is based
in the same finite box and therefore uses the same literal centered stage and
cutoff schedules. -/
structure CenteredFiniteJointCylinderData (State : Type) where
  base : Nat
  states : List State
  coefficient : State → Q'
  roots : State → State → List (List Nat)
  predicate : State → State → List Bool → Bool
  rootsCanonical : ∀ left right root,
    root ∈ roots left right →
      root ∈ canonicalSurfacePolymers base

def centeredFinitePairSequence
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (left right : State) (stage : Nat) : Q' :=
  couplingParametricCenteredRecedingCylinderSequence
    coupling hcoupling data.base (data.roots left right)
      (data.predicate left right) stage

def centeredFinitePairLimit
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (data : CenteredFiniteJointCylinderData State)
    (left right : State) : CReal :=
  couplingParametricCenteredRecedingCylinderLimitAtAnchor
    coupling hcoupling hle (data.predicate left right)
      (data.rootsCanonical left right)

@[simp] theorem centeredFinitePairLimit_approx
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (data : CenteredFiniteJointCylinderData State)
    (left right : State) (stage : Nat) :
    (centeredFinitePairLimit coupling hcoupling hle
      data left right).approx stage =
      centeredFinitePairSequence coupling hcoupling
        data left right stage := rfl

/-! ## 2. Finite list assembly at the `CReal` level -/

def listCRealSum {A : Type} (value : A → CReal) : List A → CReal
  | [] => CReal.czero
  | head :: tail => CReal.add (value head) (listCRealSum value tail)

theorem listCRealSum_approx {A : Type} (value : A → CReal) :
    ∀ (source : List A) (stage : Nat),
      (listCRealSum value source).approx stage =
        listQSum (fun item => (value item).approx stage) source
  | [], _ => rfl
  | head :: tail, stage => by
      change (value head).approx stage +
          (listCRealSum value tail).approx stage =
        (value head).approx stage +
          listQSum (fun item => (value item).approx stage) tail
      rw [listCRealSum_approx value tail stage]

/-- Rational finite joint quadratic at one literal centered stage. -/
def centeredFiniteJointCylinderSequence
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (stage : Nat) : Q' :=
  finiteJointQuadratic data.states data.coefficient
    (fun left right =>
      centeredFinitePairSequence coupling hcoupling
        data left right stage)

/-- Constructive-real value of the finite signed centered joint quadratic. -/
def centeredFiniteJointCylinderQuadratic
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (data : CenteredFiniteJointCylinderData State) : CReal :=
  listCRealSum
    (fun left => listCRealSum
      (fun right => CReal.mul
        (CReal.ofQ'
          (data.coefficient left * data.coefficient right))
        (centeredFinitePairLimit
          coupling hcoupling hle data left right))
      data.states)
    data.states

/-- The constructive-real quadratic has exactly the common-stage rational
finite joint quadratic as every approximation. -/
theorem centeredFiniteJointCylinderQuadratic_approx_eqv
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (data : CenteredFiniteJointCylinderData State)
    (stage : Nat) :
    (centeredFiniteJointCylinderQuadratic
        coupling hcoupling hle data).approx stage ≈
      centeredFiniteJointCylinderSequence
        coupling hcoupling data stage := by
  unfold centeredFiniteJointCylinderQuadratic
    centeredFiniteJointCylinderSequence finiteJointQuadratic
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro left
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro right
  exact Q'.eqv_refl _

/-! ## 3. Explicit half-time/centered chart alignment -/

/-- The natural half-time box is the one-step larger, opposite-parity box
adjacent to the literal centered stage.  This arithmetic identity prevents an
impossible same-volume alignment from being hidden in the bridge. -/
theorem centralAmbient_eq_centeredStageBase_add_one
    (base stage : Nat) :
    centralAmbient (base + stage) =
      centeredRecedingStageBase base stage + 1 := by
  unfold centralAmbient centralExtent centeredRecedingStageBase
    centeredRecedingStageRadius centeredBoxBase
  omega

/-- Checked parity fence: the half-time ambient box can never be literally
the same box as a centered receding stage. -/
theorem centralAmbient_ne_centeredStageBase
    (half base stage : Nat) :
    centralAmbient half ≠ centeredRecedingStageBase base stage := by
  unfold centralAmbient centralExtent centeredRecedingStageBase
    centeredRecedingStageRadius centeredBoxBase
  omega

/-- Pairwise chart alignment.  It exposes the adjacent-volume identity,
legal support codes, and a uniform rational comparison between every
half-time ambient pair event and its centered receding counterpart. -/
def CentralHalfTimeCenteredPairChart
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (chartEpsilon : Nat → Q') : Prop :=
  (∀ stage,
    centralAmbient (halfSchedule stage) =
      centeredRecedingStageBase data.base stage + 1) ∧
  (∀ stage state, state ∈ data.states →
    supportAt stage state ∈
      centralHalfSupportSpace (halfSchedule stage)) ∧
  (∀ stage, (0 : Q') ≤ chartEpsilon stage) ∧
  ∀ stage left right,
    left ∈ data.states → right ∈ data.states →
    Q'.abs
        (centralAmbientSupportPairLaw coupling hcoupling
            (centeredRecedingStageCutoff data.base stage)
            (halfSchedule stage)
            (supportAt stage left) (supportAt stage right) -
          centeredFinitePairSequence coupling hcoupling
            data left right stage) ≤
      chartEpsilon stage

/-- Exact zero-extension/reindexing of the fixed finite coefficient list into
the complete half-time support space. -/
def CentralHalfTimeCoefficientEmbedding
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (supportCoefficient : Nat → List Nat → Q') : Prop :=
  ∀ stage,
    centralAmbientSupportQuadratic coupling hcoupling
        (centeredRecedingStageCutoff data.base stage)
        (halfSchedule stage) (supportCoefficient stage) ≈
      finiteJointQuadratic data.states data.coefficient
        (fun left right =>
          centralAmbientSupportPairLaw coupling hcoupling
            (centeredRecedingStageCutoff data.base stage)
            (halfSchedule stage)
            (supportAt stage left) (supportAt stage right))

/-- Quadratic error contributed by the adjacent-volume centered chart. -/
def centralHalfTimeCenteredChartModulus
    {State : Type}
    (data : CenteredFiniteJointCylinderData State)
    (chartEpsilon : Nat → Q') (stage : Nat) : Q' :=
  (coefficientL1 data.states data.coefficient *
      coefficientL1 data.states data.coefficient) *
    chartEpsilon stage

private theorem sub_eqv_left_local {a a' b : Q'}
    (h : a ≈ a') : a - b ≈ a' - b :=
  Q'.add_eqv_congr' h (Q'.eqv_refl (-b))

/-- The pairwise adjacent-volume comparison lifts to the exact finite
quadratic chart modulus. -/
theorem centralHalfTimeCenteredQuadratic_abs_sub_le
    {State : Type}
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (supportCoefficient : Nat → List Nat → Q')
    (chartEpsilon : Nat → Q')
    (hchart : CentralHalfTimeCenteredPairChart
      coupling hcoupling data halfSchedule supportAt chartEpsilon)
    (hembedding : CentralHalfTimeCoefficientEmbedding
      coupling hcoupling data halfSchedule supportAt supportCoefficient)
    (stage : Nat) :
    Q'.abs
        (centralAmbientSupportQuadratic coupling hcoupling
            (centeredRecedingStageCutoff data.base stage)
            (halfSchedule stage) (supportCoefficient stage) -
          centeredFiniteJointCylinderSequence
            coupling hcoupling data stage) ≤
      centralHalfTimeCenteredChartModulus data chartEpsilon stage := by
  unfold CentralHalfTimeCenteredPairChart at hchart
  have hfinite := finiteJointQuadratic_abs_sub_le_square
    data.states data.coefficient
    (fun left right =>
      centralAmbientSupportPairLaw coupling hcoupling
        (centeredRecedingStageCutoff data.base stage)
        (halfSchedule stage)
        (supportAt stage left) (supportAt stage right))
    (fun left right =>
      centeredFinitePairSequence coupling hcoupling
        data left right stage)
    (chartEpsilon stage) (hchart.2.2.1 stage)
    (fun left right hleft hright =>
      hchart.2.2.2 stage left right hleft hright)
  have hdifference :
      centralAmbientSupportQuadratic coupling hcoupling
          (centeredRecedingStageCutoff data.base stage)
          (halfSchedule stage) (supportCoefficient stage) -
        centeredFiniteJointCylinderSequence
          coupling hcoupling data stage ≈
      finiteJointQuadratic data.states data.coefficient
          (fun left right =>
            centralAmbientSupportPairLaw coupling hcoupling
              (centeredRecedingStageCutoff data.base stage)
              (halfSchedule stage)
              (supportAt stage left) (supportAt stage right)) -
        finiteJointQuadratic data.states data.coefficient
          (fun left right =>
            centeredFinitePairSequence coupling hcoupling
              data left right stage) := by
    unfold centeredFiniteJointCylinderSequence
    exact sub_eqv_left_local (hembedding stage)
  unfold centralHalfTimeCenteredChartModulus
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hfinite

/-! ## 4. Vanishing-error constructive-real order closure -/

/-- A constructive real whose approximations are bounded below by an explicit
eventually vanishing rational error is soundly nonnegative.  This is the
vanishing-error counterpart of
`FiniteWeightedGramCRealLimit.creal_geRat_zero_of_approx_eqv`. -/
theorem creal_geRat_zero_of_approx_ge_vanishing
    (value : CReal) (modulus : Nat → Q')
    (hlower : ∀ stage, -modulus stage ≤ value.approx stage)
    (hvanishes : ∀ epsilon, (0 : Q') < epsilon →
      ∃ threshold, ∀ stage, threshold ≤ stage →
        modulus stage ≤ epsilon) :
    ExpPos.geRat value 0 := by
  intro epsilon hepsilon
  obtain ⟨threshold, hthreshold⟩ := hvanishes epsilon hepsilon
  refine ⟨threshold, fun stage hstage => ?_⟩
  have hmodulus := hthreshold stage hstage
  have hneg : -epsilon ≤ -modulus stage :=
    Q'.neg_le_neg hmodulus
  have hzero : (0 : Q') ≤ -modulus stage + epsilon := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_add_self_eqv epsilon))
      (Q'.add_le_add_right (-epsilon) (-modulus stage)
        epsilon hneg)
  exact Q'.le_trans' _ _ _ hzero
    (Q'.add_le_add_right (-modulus stage) (value.approx stage)
      epsilon (hlower stage))

/-- Literal quadratic boundary modulus along a half-time schedule. -/
def centralHalfTimeBoundaryModulus
    (halfSchedule floorSchedule : Nat → Nat)
    (supportCoefficient : Nat → List Nat → Q')
    (stage : Nat) : Q' :=
  (coefficientL1
      (centralHalfSupportSpace (halfSchedule stage))
      (supportCoefficient stage) *
    coefficientL1
      (centralHalfSupportSpace (halfSchedule stage))
      (supportCoefficient stage)) *
    centralSupportPairBoundaryEpsilon
      (halfSchedule stage) (floorSchedule stage)

/-- Total lower-error modulus: corrected-slab conditioning error plus the
adjacent-volume centered-chart error. -/
def centralHalfTimeCenteredTotalModulus
    {State : Type}
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule floorSchedule : Nat → Nat)
    (supportCoefficient : Nat → List Nat → Q')
    (chartEpsilon : Nat → Q') (stage : Nat) : Q' :=
  centralHalfTimeBoundaryModulus
      halfSchedule floorSchedule supportCoefficient stage +
    centralHalfTimeCenteredChartModulus data chartEpsilon stage

def CentralHalfTimeCarrierSchedule
    (halfSchedule floorSchedule : Nat → Nat) : Prop :=
  ∀ stage,
    CentralSupportPairCarrierFloors
      (halfSchedule stage) (floorSchedule stage)

def CentralHalfTimeCenteredTotalModulusVanishes
    {State : Type}
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule floorSchedule : Nat → Nat)
    (supportCoefficient : Nat → List Nat → Q')
    (chartEpsilon : Nat → Q') : Prop :=
  ∀ epsilon, (0 : Q') < epsilon →
    ∃ threshold, ∀ stage, threshold ≤ stage →
      centralHalfTimeCenteredTotalModulus data
        halfSchedule floorSchedule supportCoefficient
          chartEpsilon stage ≤ epsilon

private theorem reference_add_value_sub_reference_eqv
    (reference value : Q') :
    reference + (value + (-reference)) ≈ value := by
  refine Q'.eqv_trans _ ((reference + value) + (-reference)) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv reference value (-reference))) ?_
  refine Q'.eqv_trans _ ((value + reference) + (-reference)) _
    (Q'.add_eqv_congr_right _ _ (-reference)
      (Q'.add_comm_eqv reference value)) ?_
  refine Q'.eqv_trans _ (value + (reference + (-reference))) _
    (Q'.add_assoc_eqv value reference (-reference)) ?_
  refine Q'.eqv_trans _ (value + 0) _
    (Q'.add_eqv_congr_left value _ _
      (Q'.add_neg_self_eqv reference)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' value)

/-- A reference lower bound and an absolute comparison error add at the
level of lower-error moduli. -/
private theorem ge_neg_add_of_ge_neg_and_abs_sub_le
    {value reference first second : Q'}
    (hreference : -first ≤ reference)
    (hclose : Q'.abs (value - reference) ≤ second) :
    -(first + second) ≤ value := by
  have hnegativeDifference :
      -second ≤ value - reference :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hclose)
      (neg_abs_le (value - reference))
  have hadd := Q'.add_le_add hreference hnegativeDifference
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.neg_add_eqv first second))
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (reference_add_value_sub_reference_eqv reference value)))

/-- Centered constructive-real reflection positivity for the given finite
positive-time cylinder polynomial, conditional only on the explicitly named
half-time chart/reindex and carrier-floor schedules. -/
theorem centeredFiniteJointCylinderQuadratic_geRat_zero_of_halfTime
    {State : Type}
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (data : CenteredFiniteJointCylinderData State)
    (halfSchedule floorSchedule : Nat → Nat)
    (supportAt : Nat → State → List Nat)
    (supportCoefficient : Nat → List Nat → Q')
    (chartEpsilon : Nat → Q')
    (hchart : CentralHalfTimeCenteredPairChart
      coupling hcoupling data halfSchedule supportAt chartEpsilon)
    (hembedding : CentralHalfTimeCoefficientEmbedding
      coupling hcoupling data halfSchedule supportAt supportCoefficient)
    (hcarrier : CentralHalfTimeCarrierSchedule
      halfSchedule floorSchedule)
    (hvanishes : CentralHalfTimeCenteredTotalModulusVanishes data
      halfSchedule floorSchedule supportCoefficient chartEpsilon) :
    ExpPos.geRat
      (centeredFiniteJointCylinderQuadratic
        coupling hcoupling hle data) 0 := by
  apply creal_geRat_zero_of_approx_ge_vanishing
    (centeredFiniteJointCylinderQuadratic
      coupling hcoupling hle data)
    (centralHalfTimeCenteredTotalModulus data
      halfSchedule floorSchedule supportCoefficient chartEpsilon)
  · intro stage
    have hambient := centralAmbientSupportQuadratic_ge_neg_modulus
      hcoupling hle
      (centeredRecedingStageCutoff data.base stage)
      (halfSchedule stage) (floorSchedule stage)
      (hcarrier stage) (supportCoefficient stage)
    have hcloseRaw := centralHalfTimeCenteredQuadratic_abs_sub_le
      coupling hcoupling data halfSchedule supportAt supportCoefficient
      chartEpsilon hchart hembedding stage
    have hclose :
        Q'.abs
            (centeredFiniteJointCylinderSequence
                coupling hcoupling data stage -
              centralAmbientSupportQuadratic coupling hcoupling
                (centeredRecedingStageCutoff data.base stage)
                (halfSchedule stage) (supportCoefficient stage)) ≤
          centralHalfTimeCenteredChartModulus
            data chartEpsilon stage := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
            (centeredFiniteJointCylinderSequence
              coupling hcoupling data stage)
            (centralAmbientSupportQuadratic coupling hcoupling
              (centeredRecedingStageCutoff data.base stage)
              (halfSchedule stage) (supportCoefficient stage))))
        hcloseRaw
    have hcentered := ge_neg_add_of_ge_neg_and_abs_sub_le
      hambient hclose
    have happ := centeredFiniteJointCylinderQuadratic_approx_eqv
      coupling hcoupling hle data stage
    unfold centralHalfTimeCenteredTotalModulus
    exact Q'.le_trans' _ _ _ hcentered
      (Q'.le_of_eqv (Q'.eqv_symm happ))
  · exact hvanishes

#print axioms centeredFinitePairLimit_approx
#print axioms listCRealSum_approx
#print axioms centeredFiniteJointCylinderQuadratic_approx_eqv
#print axioms centralAmbient_eq_centeredStageBase_add_one
#print axioms centralAmbient_ne_centeredStageBase
#print axioms centralHalfTimeCenteredQuadratic_abs_sub_le
#print axioms creal_geRat_zero_of_approx_ge_vanishing
#print axioms centeredFiniteJointCylinderQuadratic_geRat_zero_of_halfTime

end YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
