/-
# Quantitative conditional tails for completed BF4 heat products

`BF4CompletedProductTailBound` proves that a literal 23-factor completed heat
product differs from its simultaneous finite prefix by at most

    bf4ProductTail(T) = 23 * allLabelHaarCeiling^22 * T.

This module propagates that exact error through the next physical operation:
multiply each retained path channel by a common nonnegative rational path
weight and sum over a finite retained path carrier.  The resulting conditional
kernel error is exactly

    bf4ProductTail(T) * sum_path pathWeight(path).

No path-count or potential-oscillation maximum is inserted.

## Honest scope

The spacing specialization uses a common rational nome `0 < w <= 1/2` and
factor coordinates depending on the retained path.  A final wrapper takes
`pathWeight(path)` to be the actual product of nonnegative local potential
weights.  This remains a literal completed pointwise heat carrier; it does
not identify that carrier with the interacting BF4 spin-foam slab.

## Constructivity

The proof is finite-list induction in the semantic
`CReal.leRat` / `ExpPos.geRat` orders.  Scaling is used only by nonnegative
rational weights.  There is no `Classical.*`, `Real`, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedProductTailBound
import YMGap.Continuum.BF4CompletedConditionalLimitBridge

namespace YMGap.Continuum.BF4CompletedConditionalTailBound

open YMGap.Constructive
open YMGap.Continuum.BF4CompletedConditionalLimitBridge
open YMGap.Continuum.BF4CompletedProductTailBound
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Weighted finite path sums -/

/-- Rational finite path sum after multiplying each channel by its supplied
path weight. -/
def weightedRationalPathSum {Path : Type}
    (pathWeight finiteValue : Path → Q')
    (paths : List Path) : Q' :=
  rationalPathSum
    (fun path =>
      pathWeight path * finiteValue path)
    paths

/-- Completed finite path sum after multiplying each completed channel by
the rational path weight. -/
def completedWeightedPathSum {Path : Type}
    (pathWeight : Path → Q')
    (value : Path → CReal)
    (paths : List Path) : CReal :=
  completedPathSum
    (fun path =>
      CReal.mul
        (CReal.ofQ' (pathWeight path))
        (value path))
    paths

/-- The exact algebra used at one list-cons step:

`w*(k+e) + (R+e*W) = (w*k+R) + e*(w+W)`.
-/
private theorem weighted_tail_regroup
    (weight finiteValue error
      restValue restWeight : Q') :
    weight * (finiteValue + error) +
          (restValue + error * restWeight) ≈
      (weight * finiteValue + restValue) +
        error * (weight + restWeight) := by
  have hexpandHead :
      weight * (finiteValue + error) ≈
        weight * finiteValue + weight * error :=
    Q'.mul_add_eqv weight finiteValue error
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      _ _ _ hexpandHead) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner
      (weight * finiteValue)
      (weight * error)
      restValue
      (error * restWeight)) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right
      (weight * error)
      (error * weight)
      (error * restWeight)
      (Q'.mul_comm_eqv weight error)) ?_
  exact Q'.eqv_symm
    (Q'.mul_add_eqv
      error weight restWeight)

/-- A common semantic upper error tensors through a nonnegative weighted
finite path sum. -/
theorem completedWeightedPathSum_upper
    {Path : Type}
    (pathWeight : Path → Q')
    (value : Path → CReal)
    (finiteValue : Path → Q')
    (tail : Q')
    (htail0 : (0 : Q') ≤ tail) :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path) →
      (∀ path, path ∈ paths →
        CReal.leRat
          (value path)
          (finiteValue path + tail)) →
      CReal.leRat
        (completedWeightedPathSum
          pathWeight value paths)
        (weightedRationalPathSum
            pathWeight finiteValue paths +
          tail * rationalPathSum pathWeight paths)
  | [], _, _ => by
      apply CReal.leRat_of_eventually
      refine ⟨0, fun _ _ => ?_⟩
      change
        (0 : Q') ≤
          (0 : Q') + tail * 0
      exact Q'.add_le_self_of_nonneg 0 _
        (Q'.mul_nonneg _ _
          htail0 (Q'.le_refl' 0))
  | path :: rest, pathWeight_nonnegative, path_upper => by
      have hhead :
          CReal.leRat
            (CReal.mul
              (CReal.ofQ' (pathWeight path))
              (value path))
            (pathWeight path *
              (finiteValue path + tail)) :=
        CReal.leRat_smul_nonneg
          (pathWeight_nonnegative
            path List.mem_cons_self)
          (path_upper path List.mem_cons_self)
      have hrest :
          CReal.leRat
            (completedWeightedPathSum
              pathWeight value rest)
            (weightedRationalPathSum
                pathWeight finiteValue rest +
              tail *
                rationalPathSum pathWeight rest) :=
        completedWeightedPathSum_upper
          pathWeight value finiteValue tail htail0
          rest
          (fun item hitem =>
            pathWeight_nonnegative item
              (List.mem_cons_of_mem path hitem))
          (fun item hitem =>
            path_upper item
              (List.mem_cons_of_mem path hitem))
      have hsum :=
        CReal.leRat_add hhead hrest
      exact CReal.leRat_mono hsum
        (Q'.le_of_eqv
          (weighted_tail_regroup
            (pathWeight path)
            (finiteValue path)
            tail
            (weightedRationalPathSum
              pathWeight finiteValue rest)
            (rationalPathSum
              pathWeight rest)))

/-- A common semantic lower error tensors through the same nonnegative
weighted finite path sum. -/
theorem completedWeightedPathSum_lower
    {Path : Type}
    (pathWeight : Path → Q')
    (value : Path → CReal)
    (finiteValue : Path → Q')
    (tail : Q') :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path) →
      (∀ path, path ∈ paths →
        ExpPos.geRat
          (value path)
          (finiteValue path + -tail)) →
      ExpPos.geRat
        (completedWeightedPathSum
          pathWeight value paths)
        (weightedRationalPathSum
            pathWeight finiteValue paths +
          -(tail * rationalPathSum pathWeight paths))
  | [], _, _ => by
      apply ExpPos.geRat_of_eventually
      refine ⟨0, fun _ _ => ?_⟩
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left
            0 (-(tail * 0)) 0
            (Q'.eqv_trans _ _ _
              (Q'.neg_eqv_congr
                (tail * 0) 0
                (Q'.mul_zero_eqv tail))
              (Q'.eqv_refl 0)))
          (Q'.eqv_refl 0))
  | path :: rest, pathWeight_nonnegative, path_lower => by
      have hhead :
          ExpPos.geRat
            (CReal.mul
              (CReal.ofQ' (pathWeight path))
              (value path))
            (pathWeight path *
              (finiteValue path + -tail)) :=
        YMGap.Constructive.SU3CharFactor.geRat_smul_nonneg
          (pathWeight_nonnegative
            path List.mem_cons_self)
          (path_lower path List.mem_cons_self)
      have hrest :
          ExpPos.geRat
            (completedWeightedPathSum
              pathWeight value rest)
            (weightedRationalPathSum
                pathWeight finiteValue rest +
              -(tail *
                rationalPathSum pathWeight rest)) :=
        completedWeightedPathSum_lower
          pathWeight value finiteValue tail
          rest
          (fun item hitem =>
            pathWeight_nonnegative item
              (List.mem_cons_of_mem path hitem))
          (fun item hitem =>
            path_lower item
              (List.mem_cons_of_mem path hitem))
      have hrest' :
          ExpPos.geRat
            (completedWeightedPathSum
              pathWeight value rest)
            (weightedRationalPathSum
                pathWeight finiteValue rest +
              (-tail) *
                rationalPathSum pathWeight rest) := by
        exact ExpPos.geRat_mono hrest
          (Q'.le_of_eqv
            (Q'.add_eqv_congr_left
              (weightedRationalPathSum
                pathWeight finiteValue rest)
              ((-tail) *
                rationalPathSum pathWeight rest)
              (-(tail *
                rationalPathSum pathWeight rest))
              (Q'.neg_mul_eqv
                tail
                (rationalPathSum
                  pathWeight rest))))
      have hsum :=
        SumOfSquares.geRat_add hhead hrest'
      have hintermediate :
          ExpPos.geRat
            (completedWeightedPathSum
              pathWeight value (path :: rest))
            (weightedRationalPathSum
                pathWeight finiteValue (path :: rest) +
              (-tail) *
                rationalPathSum
                  pathWeight (path :: rest)) :=
        ExpPos.geRat_mono hsum
          (Q'.le_of_eqv
            (Q'.eqv_symm
              (weighted_tail_regroup
                (pathWeight path)
                (finiteValue path)
                (-tail)
                (weightedRationalPathSum
                  pathWeight finiteValue rest)
                (rationalPathSum
                  pathWeight rest))))
      exact ExpPos.geRat_mono hintermediate
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_left
            (weightedRationalPathSum
              pathWeight finiteValue (path :: rest))
            (-(tail *
              rationalPathSum
                pathWeight (path :: rest)))
            ((-tail) *
              rationalPathSum
                pathWeight (path :: rest))
            (Q'.eqv_symm
              (Q'.neg_mul_eqv
                tail
                (rationalPathSum
                  pathWeight (path :: rest))))))

/-! ## 2. Exact BF4 spacing conditional kernel -/

/-- Simultaneous finite-prefix conditional BF4 kernel. -/
def spacingFiniteBF4ConditionalKernel
    {Path Factor : Type}
    (paths : List Path)
    (factors : List Factor)
    (w : Q')
    (coordinate : Path → Factor → Q')
    (pathWeight : Path → Q')
    (M : Nat) : Q' :=
  weightedRationalPathSum
    pathWeight
    (fun path =>
      spacingFiniteFactorProduct
        factors w (coordinate path) M)
    paths

/-- Completed conditional BF4 kernel with the same rational path weights. -/
def spacingCompletedBF4ConditionalKernel
    {Path Factor : Type}
    (paths : List Path)
    (factors : List Factor)
    (w : Q')
    (coordinate : Path → Factor → Q')
    (pathWeight : Path → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ path factor,
        (-(1 : Q')) ≤ coordinate path factor)
    (coordinate_upper :
      ∀ path factor,
        coordinate path factor ≤ (1 : Q')) :
    CReal :=
  completedWeightedPathSum
    pathWeight
    (fun path =>
      spacingCompletedFactorProduct
        factors w (coordinate path)
        hw0 hw
        (coordinate_lower path)
        (coordinate_upper path))
    paths

/-- Exact conditional tail: the exact 23-factor kinetic tail multiplied by
the literal rational total path-potential mass. -/
def bf4ConditionalTail
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (kineticTail : Q') : Q' :=
  bf4ProductTail kineticTail *
    rationalPathSum pathWeight paths

/-- Exact semantic upper bound for the completed conditional BF4 kernel. -/
theorem spacingCompletedBF4ConditionalKernel_upper
    {Path Factor : Type}
    (paths : List Path)
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q')
    (coordinate : Path → Factor → Q')
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ path factor,
        (-(1 : Q')) ≤ coordinate path factor)
    (coordinate_upper :
      ∀ path factor,
        coordinate path factor ≤ (1 : Q'))
    (M : Nat) :
    CReal.leRat
      (spacingCompletedBF4ConditionalKernel
        paths factors w coordinate pathWeight
        hw0 hw coordinate_lower coordinate_upper)
      (spacingFiniteBF4ConditionalKernel
          paths factors w coordinate pathWeight M +
        bf4ConditionalTail
          paths pathWeight
          (spacingClosedTail w (2 + M))) := by
  exact completedWeightedPathSum_upper
    pathWeight
    (fun path =>
      spacingCompletedFactorProduct
        factors w (coordinate path)
        hw0 hw
        (coordinate_lower path)
        (coordinate_upper path))
    (fun path =>
      spacingFiniteFactorProduct
        factors w (coordinate path) M)
    (bf4ProductTail
      (spacingClosedTail w (2 + M)))
    (Q'.mul_nonneg _ _
      (by decide)
      (spacingClosedTail_nonnegative
        hw0 (2 + M)))
    paths
    pathWeight_nonnegative
    (fun path hpath =>
      spacingCompletedBF4Product_le_finite_add_tail
        factors factor_count
        w (coordinate path)
        hw0 hw
        (coordinate_lower path)
        (coordinate_upper path)
        M)

/-- Exact semantic lower bound for the completed conditional BF4 kernel. -/
theorem spacingCompletedBF4ConditionalKernel_lower
    {Path Factor : Type}
    (paths : List Path)
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q')
    (coordinate : Path → Factor → Q')
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ path factor,
        (-(1 : Q')) ≤ coordinate path factor)
    (coordinate_upper :
      ∀ path factor,
        coordinate path factor ≤ (1 : Q'))
    (M : Nat) :
    ExpPos.geRat
      (spacingCompletedBF4ConditionalKernel
        paths factors w coordinate pathWeight
        hw0 hw coordinate_lower coordinate_upper)
      (spacingFiniteBF4ConditionalKernel
          paths factors w coordinate pathWeight M +
        -bf4ConditionalTail
          paths pathWeight
          (spacingClosedTail w (2 + M))) := by
  exact completedWeightedPathSum_lower
    pathWeight
    (fun path =>
      spacingCompletedFactorProduct
        factors w (coordinate path)
        hw0 hw
        (coordinate_lower path)
        (coordinate_upper path))
    (fun path =>
      spacingFiniteFactorProduct
        factors w (coordinate path) M)
    (bf4ProductTail
      (spacingClosedTail w (2 + M)))
    paths
    pathWeight_nonnegative
    (fun path hpath =>
      finite_sub_tail_le_spacingCompletedBF4Product
        factors factor_count
        w (coordinate path)
        hw0 hw
        (coordinate_lower path)
        (coordinate_upper path)
        M)

/-- Type-level exact two-sided conditional-kernel corridor. -/
structure BF4CompletedConditionalTailCorridor
    (completed : CReal) (finite tail : Q') : Type where
  lower : ExpPos.geRat completed (finite + -tail)
  upper : CReal.leRat completed (finite + tail)

/-- Package the exact completed-vs-finite conditional BF4 tail. -/
def bf4CompletedConditionalTailCorridor
    {Path Factor : Type}
    (paths : List Path)
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q')
    (coordinate : Path → Factor → Q')
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ path factor,
        (-(1 : Q')) ≤ coordinate path factor)
    (coordinate_upper :
      ∀ path factor,
        coordinate path factor ≤ (1 : Q'))
    (M : Nat) :
    BF4CompletedConditionalTailCorridor
      (spacingCompletedBF4ConditionalKernel
        paths factors w coordinate pathWeight
        hw0 hw coordinate_lower coordinate_upper)
      (spacingFiniteBF4ConditionalKernel
        paths factors w coordinate pathWeight M)
      (bf4ConditionalTail
        paths pathWeight
        (spacingClosedTail w (2 + M))) where
  lower :=
    spacingCompletedBF4ConditionalKernel_lower
      paths factors factor_count
      w coordinate pathWeight pathWeight_nonnegative
      hw0 hw coordinate_lower coordinate_upper M
  upper :=
    spacingCompletedBF4ConditionalKernel_upper
      paths factors factor_count
      w coordinate pathWeight pathWeight_nonnegative
      hw0 hw coordinate_lower coordinate_upper M

/-! ## 3. Actual nonnegative interior-potential product wrapper -/

/-- The exact conditional tail when the path weight is the product of local
potential insertions. -/
def bf4PotentialConditionalTail
    {State : Type}
    (paths : List (List State))
    (potential : State → Q')
    (kineticTail : Q') : Q' :=
  bf4ConditionalTail
    paths
    (pathPotentialProduct potential)
    kineticTail

/-- The potential-weight specialization is definitionally the existing
`completedConditionalPathPushforward`, with trivial external source/target
carriers and the spacing-completed BF4 kinetic channel retained as the path
coordinate. -/
theorem spacingCompletedBF4ConditionalKernel_eq_pushforward
    {State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w : Q')
    (coordinate :
      List State → Factor → Q')
    (potential : State → Q')
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ path factor,
        (-(1 : Q')) ≤ coordinate path factor)
    (coordinate_upper :
      ∀ path factor,
        coordinate path factor ≤ (1 : Q')) :
    spacingCompletedBF4ConditionalKernel
        paths factors w coordinate
        (pathPotentialProduct potential)
        hw0 hw coordinate_lower coordinate_upper =
      completedConditionalPathPushforward
        paths
        (fun (_source : Unit) (_target : Unit) path =>
          spacingCompletedFactorProduct
            factors w (coordinate path)
            hw0 hw
            (coordinate_lower path)
            (coordinate_upper path))
        potential () () :=
  rfl

/-- Quantitative conditional BF4 corridor with the actual nonnegative
interior-potential product on every retained path. -/
def bf4PotentialCompletedConditionalTailCorridor
    {State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (factor_count :
      factors.length = bf4SpatialCycleCount)
    (w : Q')
    (coordinate :
      List State → Factor → Q')
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (hw0 : (0 : Q') < w)
    (hw : w ≤ half)
    (coordinate_lower :
      ∀ path factor,
        (-(1 : Q')) ≤ coordinate path factor)
    (coordinate_upper :
      ∀ path factor,
        coordinate path factor ≤ (1 : Q'))
    (M : Nat) :
    BF4CompletedConditionalTailCorridor
      (spacingCompletedBF4ConditionalKernel
        paths factors w coordinate
        (pathPotentialProduct potential)
        hw0 hw coordinate_lower coordinate_upper)
      (spacingFiniteBF4ConditionalKernel
        paths factors w coordinate
        (pathPotentialProduct potential) M)
      (bf4PotentialConditionalTail
        paths potential
        (spacingClosedTail w (2 + M))) := by
  exact bf4CompletedConditionalTailCorridor
    paths factors factor_count
    w coordinate
    (pathPotentialProduct potential)
    (fun path hpath =>
      pathPotentialProduct_nonnegative
        potential_nonnegative path)
    hw0 hw coordinate_lower coordinate_upper M

/-! ## Axiom gates -/

#print axioms weightedRationalPathSum
#print axioms completedWeightedPathSum_upper
#print axioms completedWeightedPathSum_lower
#print axioms spacingCompletedBF4ConditionalKernel_upper
#print axioms spacingCompletedBF4ConditionalKernel_lower
#print axioms bf4CompletedConditionalTailCorridor
#print axioms spacingCompletedBF4ConditionalKernel_eq_pushforward
#print axioms bf4PotentialCompletedConditionalTailCorridor

end YMGap.Continuum.BF4CompletedConditionalTailBound
