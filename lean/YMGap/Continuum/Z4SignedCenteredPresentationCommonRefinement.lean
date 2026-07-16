/-
# Common-refinement descent for signed centered cylinder presentations

Two signed centered presentations are aligned-equivalent when their receding
cylinder events agree exactly after both stage schedules are advanced to one
explicit common diagonal base.  This is a quotient-free, constructive
relation: the common base and every event equality are data, not a semantic
extensionality axiom.

The uniform-shift volume theorem makes each centered diagonal Cauchy.  Using a
single common representation cutoff, the two boundary comparisons and the two
outer cutoff tails fit inside the already prescribed presentation-comparison
coefficient.  Hence aligned-equivalent presentations have equivalent Bishop
real values throughout the derived strong-coupling window.
-/

import YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

namespace YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCutoffTail
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Exact common alignment -/

def signedCenteredPresentationAlignedStage
    (presentation : SignedCenteredCylinderPresentation)
    (absoluteBase : Nat) : Nat :=
  absoluteBase - signedCenteredPresentationDiagonalBase presentation

/-- Exact eventual equality after advancing both receding schedules to an
explicit common diagonal base. -/
def SignedCenteredPresentationAlignedEquivalent
    (left right : SignedCenteredCylinderPresentation) : Prop :=
  ∃ commonBase : Nat,
    signedCenteredPresentationDiagonalBase left ≤ commonBase ∧
    signedCenteredPresentationDiagonalBase right ≤ commonBase ∧
    ∀ absoluteBase : Nat, commonBase ≤ absoluteBase →
      centeredRecedingCylinderEvent
          (signedCenteredPresentationDiagonalBase left)
          (signedCenteredPresentationAlignedStage left absoluteBase)
          left.chart.roots left.predicate =
        centeredRecedingCylinderEvent
          (signedCenteredPresentationDiagonalBase right)
          (signedCenteredPresentationAlignedStage right absoluteBase)
          right.chart.roots right.predicate

theorem signedCenteredPresentationAlignedEquivalent_refl
    (presentation : SignedCenteredCylinderPresentation) :
    SignedCenteredPresentationAlignedEquivalent
      presentation presentation := by
  refine ⟨signedCenteredPresentationDiagonalBase presentation,
    Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro absoluteBase _
  rfl

theorem signedCenteredPresentationAlignedEquivalent_symm
    {left right : SignedCenteredCylinderPresentation}
    (h : SignedCenteredPresentationAlignedEquivalent left right) :
    SignedCenteredPresentationAlignedEquivalent right left := by
  rcases h with ⟨commonBase, hleft, hright, hevent⟩
  exact ⟨commonBase, hright, hleft,
    fun absoluteBase habsolute => (hevent absoluteBase habsolute).symm⟩

theorem signedCenteredPresentationAlignedEquivalent_trans
    {first middle last : SignedCenteredCylinderPresentation}
    (hfirst : SignedCenteredPresentationAlignedEquivalent first middle)
    (hlast : SignedCenteredPresentationAlignedEquivalent middle last) :
    SignedCenteredPresentationAlignedEquivalent first last := by
  rcases hfirst with
    ⟨firstCommon, hfirstBase, hmiddleFirstBase, hfirstEvent⟩
  rcases hlast with
    ⟨lastCommon, hmiddleLastBase, hlastBase, hlastEvent⟩
  let commonBase := max firstCommon lastCommon
  have hfirstCommon : firstCommon ≤ commonBase := Nat.le_max_left _ _
  have hlastCommon : lastCommon ≤ commonBase := Nat.le_max_right _ _
  refine ⟨commonBase,
    Nat.le_trans hfirstBase hfirstCommon,
    Nat.le_trans hlastBase hlastCommon, ?_⟩
  intro absoluteBase habsolute
  exact Eq.trans
    (hfirstEvent absoluteBase
      (Nat.le_trans hfirstCommon habsolute))
    (hlastEvent absoluteBase
      (Nat.le_trans hlastCommon habsolute))

theorem signedCenteredPresentationAlignedEquivalent_equivalence :
    Equivalence SignedCenteredPresentationAlignedEquivalent :=
  ⟨signedCenteredPresentationAlignedEquivalent_refl,
    @signedCenteredPresentationAlignedEquivalent_symm,
    @signedCenteredPresentationAlignedEquivalent_trans⟩

/-! ## 2. Exact relations already carried by the presentation layer -/

theorem signedCenteredPresentationAlignedEquivalent_translate
    (shift : SignedZ4Vector)
    (presentation : SignedCenteredCylinderPresentation) :
    SignedCenteredPresentationAlignedEquivalent
      (presentation.translate shift) presentation := by
  refine ⟨signedCenteredPresentationDiagonalBase presentation,
    ?_, Nat.le_refl _, ?_⟩
  · exact Nat.le_refl _
  · intro absoluteBase _
    cases presentation
    rfl

theorem signedCenteredPresentationAlignedEquivalent_appendIgnored
    (presentation : SignedCenteredCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers
        (centeredBoxBase presentation.chart.radius)) :
    SignedCenteredPresentationAlignedEquivalent
      (signedCenteredCylinderPresentationAppendIgnored
        presentation extra hextra)
      presentation := by
  refine ⟨signedCenteredPresentationDiagonalBase presentation,
    ?_, Nat.le_refl _, ?_⟩
  · exact Nat.le_refl _
  · intro absoluteBase _
    exact centeredRecedingCylinderEvent_appendIgnored
      (centeredBoxBase presentation.chart.radius) _
      presentation.chart.roots extra presentation.predicate

/-! Chart/support equality alone is deliberately fenced: predicates remain
part of the observable and cannot be erased by a purported semantic quotient. -/

def emptySignedCenteredCylinderChart : SignedCenteredCylinderChart where
  center := (0, 0, 0, 0)
  radius := 0
  roots := []
  rootsCanonical := by
    intro root hroot
    cases hroot

def emptySignedCenteredTruePresentation :
    SignedCenteredCylinderPresentation :=
  ⟨emptySignedCenteredCylinderChart, fun _ => true⟩

def emptySignedCenteredFalsePresentation :
    SignedCenteredCylinderPresentation :=
  ⟨emptySignedCenteredCylinderChart, fun _ => false⟩

theorem chart_equality_does_not_imply_aligned_equivalence :
    emptySignedCenteredTruePresentation.chart =
        emptySignedCenteredFalsePresentation.chart ∧
      ¬ SignedCenteredPresentationAlignedEquivalent
        emptySignedCenteredTruePresentation
        emptySignedCenteredFalsePresentation := by
  constructor
  · rfl
  · intro hequivalent
    rcases hequivalent with
      ⟨commonBase, _, _, hevent⟩
    have heq := congrFun
      (hevent commonBase (Nat.le_refl commonBase)) []
    simp only [emptySignedCenteredTruePresentation,
      emptySignedCenteredFalsePresentation,
      centeredRecedingCylinderEvent, cylinderEvent] at heq
    exact Bool.noConfusion heq

/-! ## 3. Quantitative comparison through one common cutoff -/

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

private theorem four_edge_abs_sub_le_local
    (a b c d e epsilonAC epsilonCD epsilonDE epsilonEB : Q')
    (hAC : Q'.abs (a - c) ≤ epsilonAC)
    (hCD : Q'.abs (c - d) ≤ epsilonCD)
    (hDE : Q'.abs (d - e) ≤ epsilonDE)
    (hEB : Q'.abs (e - b) ≤ epsilonEB) :
    Q'.abs (a - b) ≤
      epsilonAC + (epsilonCD + (epsilonDE + epsilonEB)) := by
  have hAB := abs_sub_triangle_local a b c
  have hCB := abs_sub_triangle_local c b d
  have hDB := abs_sub_triangle_local d b e
  exact Q'.le_trans' _ _ _ hAB
    (Q'.add_le_add hAC
      (Q'.le_trans' _ _ _ hCB
        (Q'.add_le_add hCD
          (Q'.le_trans' _ _ _ hDB
            (Q'.add_le_add hDE hEB)))))

theorem signedCenteredPresentationComparisonModulus_of_alignedEquivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {left right : SignedCenteredCylinderPresentation}
    (hequivalent :
      SignedCenteredPresentationAlignedEquivalent left right) :
    SignedCenteredPresentationComparisonModulus
      coupling hcoupling left right := by
  rcases hequivalent with
    ⟨commonBase, hleftBase, hrightBase, hevent⟩
  intro stage
  let leftBase := signedCenteredPresentationDiagonalBase left
  let rightBase := signedCenteredPresentationDiagonalBase right
  let absoluteBase := commonBase + stage
  let leftAligned :=
    signedCenteredPresentationAlignedStage left absoluteBase
  let rightAligned :=
    signedCenteredPresentationAlignedStage right absoluteBase
  have habsolute : commonBase ≤ absoluteBase := by
    dsimp only [absoluteBase]
    omega
  have hstageLeft : stage ≤ leftAligned := by
    dsimp only [leftAligned, absoluteBase,
      signedCenteredPresentationAlignedStage, leftBase]
    omega
  have hstageRight : stage ≤ rightAligned := by
    dsimp only [rightAligned, absoluteBase,
      signedCenteredPresentationAlignedStage, rightBase]
    omega
  have hbaseEq :
      centeredRecedingStageBase leftBase leftAligned =
        centeredRecedingStageBase rightBase rightAligned := by
    unfold centeredRecedingStageBase centeredRecedingStageRadius
    apply congrArg centeredBoxBase
    dsimp only [leftAligned, rightAligned, absoluteBase,
      signedCenteredPresentationAlignedStage, leftBase, rightBase]
    omega
  have heventEq :
      centeredRecedingCylinderEvent leftBase leftAligned
          left.chart.roots left.predicate =
        centeredRecedingCylinderEvent rightBase rightAligned
          right.chart.roots right.predicate := by
    exact hevent absoluteBase habsolute
  let leftCutoff := centeredRecedingStageCutoff leftBase stage
  let rightCutoff := centeredRecedingStageCutoff rightBase stage
  let commonCutoff := leftCutoff + rightCutoff
  have hleftCutoff : leftCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  have hrightCutoff : rightCutoff ≤ commonCutoff := by
    dsimp only [commonCutoff]
    omega
  let a := couplingParametricSignedCenteredPresentationSequence
    coupling hcoupling left stage
  let b := couplingParametricSignedCenteredPresentationSequence
    coupling hcoupling right stage
  let c := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff
    (centeredRecedingStageBase leftBase stage)
    (centeredRecedingCylinderEvent leftBase stage
      left.chart.roots left.predicate)
  let d := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff
    (centeredRecedingStageBase leftBase leftAligned)
    (centeredRecedingCylinderEvent leftBase leftAligned
      left.chart.roots left.predicate)
  let e := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling commonCutoff
    (centeredRecedingStageBase rightBase stage)
    (centeredRecedingCylinderEvent rightBase stage
      right.chart.roots right.predicate)
  have hAC : Q'.abs (a - c) ≤ HalfPow.half ^ stage := by
    have hraw :=
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle
        (centeredRecedingCylinderEvent leftBase stage
          left.chart.roots left.predicate)
        hleftCutoff
    dsimp only [a, c, leftCutoff,
      couplingParametricSignedCenteredPresentationSequence,
      couplingParametricCenteredRecedingCylinderSequence] at ⊢
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm _ _))
      hraw
  have hleftVolume :=
    centeredRecedingVolumeModulus_of_anchor
      (predicate := left.predicate) hcoupling hle
      (signedCenteredPresentation_rootsCanonical left)
  have hCD : Q'.abs (c - d) ≤
      spinSummedCylinderBoundaryCoefficient left.chart.roots.length *
        HalfPow.half ^ stage := by
    have hraw := hleftVolume.2 commonCutoff hstageLeft
    dsimp only [c, d]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm _ _))
      hraw
  have hrightVolume :=
    centeredRecedingVolumeModulus_of_anchor
      (predicate := right.predicate) hcoupling hle
      (signedCenteredPresentation_rootsCanonical right)
  have hDE : Q'.abs (d - e) ≤
      spinSummedCylinderBoundaryCoefficient right.chart.roots.length *
        HalfPow.half ^ stage := by
    have hraw := hrightVolume.2 commonCutoff hstageRight
    rw [← hbaseEq, ← heventEq] at hraw
    dsimp only [d, e]
    exact hraw
  have hEB : Q'.abs (e - b) ≤ HalfPow.half ^ stage := by
    have hraw :=
      couplingParametricKCompatibleEventProbability_jointCutoff_extension_abs_le
        hcoupling hle
        (centeredRecedingCylinderEvent rightBase stage
          right.chart.roots right.predicate)
        hrightCutoff
    dsimp only [e, b, rightCutoff,
      couplingParametricSignedCenteredPresentationSequence,
      couplingParametricCenteredRecedingCylinderSequence] at ⊢
    exact hraw
  have hchain := four_edge_abs_sub_le_local a b c d e
    (HalfPow.half ^ stage)
    (spinSummedCylinderBoundaryCoefficient left.chart.roots.length *
      HalfPow.half ^ stage)
    (spinSummedCylinderBoundaryCoefficient right.chart.roots.length *
      HalfPow.half ^ stage)
    (HalfPow.half ^ stage) hAC hCD hDE hEB
  let h := HalfPow.half ^ stage
  let leftBoundary :=
    spinSummedCylinderBoundaryCoefficient left.chart.roots.length
  let rightBoundary :=
    spinSummedCylinderBoundaryCoefficient right.chart.roots.length
  let actualCoefficient :=
    ((1 : Q') + leftBoundary) + (rightBoundary + (1 : Q'))
  let comparisonCoefficient :=
    signedCenteredPresentationComparisonCoefficient left right
  have hactual :
      h + (leftBoundary * h + (rightBoundary * h + h)) ≈
        actualCoefficient * h := by
    dsimp only [actualCoefficient]
    ring_qeqv
  have hcoefficientEq :
      actualCoefficient + Q'.ofNat 2 ≈ comparisonCoefficient := by
    dsimp only [actualCoefficient, comparisonCoefficient,
      signedCenteredPresentationComparisonCoefficient,
      spinSummedJointCylinderCoefficient]
    ring_qeqv
  have hcoefficient : actualCoefficient ≤ comparisonCoefficient :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg actualCoefficient (Q'.ofNat 2)
        (by decide))
      (Q'.le_of_eqv hcoefficientEq)
  have hscaled : actualCoefficient * h ≤ comparisonCoefficient * h :=
    Q'.mul_le_mul_of_nonneg_right actualCoefficient comparisonCoefficient h
      hcoefficient (Q'.pow_nonneg HalfPow.half (by decide) stage)
  change Q'.abs (a - b) ≤ comparisonCoefficient * h
  exact Q'.le_trans' _ _ _ hchain
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hactual) hscaled)

/-! ## 4. Quotient-free descent of the constructive value -/

theorem couplingParametricSignedCenteredPresentationValueAtAnchor_respects
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {left right : SignedCenteredCylinderPresentation}
    (hequivalent :
      SignedCenteredPresentationAlignedEquivalent left right) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle left)
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle right) := by
  exact
    Z4SignedCenteredRecedingPresentation.couplingParametricSignedCenteredPresentationValue_equiv_of_comparison
      hcoupling hle
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle left)
      (signedCenteredPresentationVolumeModulus_of_anchor
        hcoupling hle right)
      (signedCenteredPresentationComparisonModulus_of_alignedEquivalent
        hcoupling hle hequivalent)

structure SignedCenteredAlignedCylinderEvaluation where
  evaluate : SignedCenteredCylinderPresentation → CReal
  respects : ∀ left right,
    SignedCenteredPresentationAlignedEquivalent left right →
      CReal.Equiv (evaluate left) (evaluate right)

def couplingParametricSignedCenteredAlignedCylinderEvaluation
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    SignedCenteredAlignedCylinderEvaluation where
  evaluate := couplingParametricSignedCenteredPresentationValueAtAnchor
    coupling hcoupling hle
  respects := fun _ _ hequivalent =>
    couplingParametricSignedCenteredPresentationValueAtAnchor_respects
      hcoupling hle hequivalent

#print axioms signedCenteredPresentationAlignedEquivalent_trans
#print axioms signedCenteredPresentationAlignedEquivalent_equivalence
#print axioms signedCenteredPresentationAlignedEquivalent_translate
#print axioms signedCenteredPresentationAlignedEquivalent_appendIgnored
#print axioms chart_equality_does_not_imply_aligned_equivalence
#print axioms signedCenteredPresentationComparisonModulus_of_alignedEquivalent
#print axioms couplingParametricSignedCenteredPresentationValueAtAnchor_respects
#print axioms couplingParametricSignedCenteredAlignedCylinderEvaluation

end YMGap.Continuum.Z4SignedCenteredPresentationCommonRefinement
