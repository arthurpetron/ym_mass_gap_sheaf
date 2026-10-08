/-
# Coherent spatial permutations on the SAME original Wilson completion

The literal adjacent swaps x0/x1 and x1/x2 satisfy the braid on ordered
source loops, full signed Wilson syntax and intrinsic temporal charts.
Their existing completed maps therefore satisfy U01 U12 U01 = U12 U01 U12,
and their composition has cube equal to the identity. These are actual
operators on one original reflected completion, not an assumed group action.

This supplies finite spatial permutation coherence at fixed width and nome.
Signed spatial reflections, continuous/continuum covariance, useful scaling
rates and the physical Hamiltonian mass gap remain separate obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomeSpatialHeadSwapCompletion
import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion

namespace YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (OrientedBF4Link)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (distSq distSq_refl)
open YMGap.Continuum.CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup
  (closeOfPointwiseNull)

local notation "hEdge" => BF4ExactSlabSpatialHeadSwapWilsonLoop.swapEntry
local notation "aEdge" => BF4ExactSlabSpatialAxisSwapWilsonLoop.swapEntry
local notation "hLoop" => BF4ExactSlabSpatialHeadSwapWilsonLoop.swapSourceLoop
local notation "aLoop" => BF4ExactSlabSpatialAxisSwapWilsonLoop.swapSourceLoop
local notation "hExpr" => BF4ExactSlabSpatialHeadSwapWilsonWindow.swapExpression
local notation "aExpr" => BF4ExactSlabSpatialAxisSwapWilsonWindow.swapExpression
local notation "hIntrinsic" => BF4WilsonAllNomeSpatialHeadSwapForm.swapIntrinsic
local notation "aIntrinsic" => BF4WilsonAllNomeSpatialAxisSwapForm.swapIntrinsic

/-- The same reverse flag survives both three-swap paths. -/
theorem swapEntry_braid (e : OrientedBF4Link) :
    hEdge (aEdge (hEdge e)) = aEdge (hEdge (aEdge e)) := by
  cases e with
  | mk link reverse =>
      change OrientedBF4Link.mk
        (BF4ExactSlabSpatialHeadSwapGeometry.swapLink
          (BF4ExactSlabSpatialAxisSwapGeometry.swapLink
            (BF4ExactSlabSpatialHeadSwapGeometry.swapLink link))) reverse =
        OrientedBF4Link.mk
          (BF4ExactSlabSpatialAxisSwapGeometry.swapLink
            (BF4ExactSlabSpatialHeadSwapGeometry.swapLink
              (BF4ExactSlabSpatialAxisSwapGeometry.swapLink link))) reverse
      rw [BF4ExactSlabSpatialHeadSwapGeometry.swapLink_braid]

private theorem sourceLoop_ext {width : Nat} (x y : SourceLoop width)
    (hs : x.start = y.start) (he : x.edges = y.edges) : x = y := by
  cases x
  cases y
  cases hs
  cases he
  rfl

/-- Equality of actual closed ordered sources, not only their characters. -/
theorem swapSourceLoop_braid {width : Nat} (loop : SourceLoop width) :
    hLoop (aLoop (hLoop loop)) = aLoop (hLoop (aLoop loop)) := by
  apply sourceLoop_ext
  · exact BF4ExactSlabSpatialHeadSwapGeometry.swapVertex_braid loop.start
  · change ((loop.edges.map hEdge).map aEdge).map hEdge =
      ((loop.edges.map aEdge).map hEdge).map aEdge
    simp only [List.map_map, Function.comp_def, swapEntry_braid]

/-- Offsets, spins, products and signed coefficients remain literal. -/
theorem swapExpression_braid {width : Nat} :
    ∀ e : WindowExpression width, hExpr (aExpr (hExpr e)) = aExpr (hExpr (aExpr e))
  | .one => rfl
  | .loop offset value spin => by
      change WindowExpression.loop offset (hLoop (aLoop (hLoop value))) spin =
        WindowExpression.loop offset (aLoop (hLoop (aLoop value))) spin
      rw [swapSourceLoop_braid]
  | .add e f => by
      change WindowExpression.add (hExpr (aExpr (hExpr e))) (hExpr (aExpr (hExpr f))) =
        WindowExpression.add (aExpr (hExpr (aExpr e))) (aExpr (hExpr (aExpr f)))
      rw [swapExpression_braid e, swapExpression_braid f]
  | .mul e f => by
      change WindowExpression.mul (hExpr (aExpr (hExpr e))) (hExpr (aExpr (hExpr f))) =
        WindowExpression.mul (aExpr (hExpr (aExpr e))) (aExpr (hExpr (aExpr f)))
      rw [swapExpression_braid e, swapExpression_braid f]
  | .smul c e => by
      change WindowExpression.smul c (hExpr (aExpr (hExpr e))) =
        WindowExpression.smul c (aExpr (hExpr (aExpr e)))
      rw [swapExpression_braid e]

private theorem intrinsic_ext {width : Nat} (x y : IntrinsicExpression width)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x = y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem swapIntrinsic_braid {width : Nat} (x : IntrinsicExpression width) :
    hIntrinsic (aIntrinsic (hIntrinsic x)) = aIntrinsic (hIntrinsic (aIntrinsic x)) := by
  apply intrinsic_ext
  · rfl
  · exact swapExpression_braid x.expression

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "H" => BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap hw0 hw1
local notation "A" => BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap hw0 hw1

/-- Both maps use the SAME original Cauchy/null quotient. -/
theorem completedSwap_braid (x : V) : H (A (H x)) = A (H (A x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact ⟨closeOfPointwiseNull (fun k => by
    change Equiv (distSq hw0 hw1 (hIntrinsic (aIntrinsic (hIntrinsic (X.seq k))))
      (aIntrinsic (hIntrinsic (aIntrinsic (X.seq k))))) czero
    rw [swapIntrinsic_braid]
    exact distSq_refl hw0 hw1 _)⟩

/-- The actual adjacent-swap product has order dividing three. No faithfulness
or continuum rotation is claimed. -/
theorem completedCycle_cube (x : V) : H (A (H (A (H (A x))))) = x := by
  rw [completedSwap_braid,
    BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_involutive,
    BF4WilsonAllNomeSpatialHeadSwapCompletion.completedSwap_involutive,
    BF4WilsonAllNomeSpatialAxisSwapCompletion.completedSwap_involutive]

end YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid

#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid.swapEntry_braid
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid.swapSourceLoop_braid
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid.swapExpression_braid
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid.swapIntrinsic_braid
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid.completedSwap_braid
#print axioms YMGap.Continuum.BF4WilsonAllNomeSpatialSwapBraid.completedCycle_cube
