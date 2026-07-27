/-
# Entrywise matrix and already-formed Gram cutoff limits

`BF4CompletedConditionalLimitBridge` proves that the common character cutoff
can be removed before or after finite retained-path conditional integration.
This module records two finite-dimensional consequences.

First, a row/column matrix carrier is represented by the constructive product
type `Row × Column`.  The conditional cutoff limit is proved simultaneously
for every entry on supplied finite row, column, and target lists.

Second, a separately supplied, already-formed rational quadratic/Gram path
channel is multiplied by a nonnegative rational path weight and summed over a
finite path list.  Under honest factorwise convergence and a uniform bound on
the completed quadratic approximations, the literal rational weighted
quadratic sums converge to their completed finite sum.  If both the cutoff
quadratics and completed quadratics are supplied as nonnegative, nonnegativity
holds before and after cutoff removal.

Crucial fence: entrywise scalar convergence or entrywise scalar order is not
used to infer a Loewner/CP statement.  The quadratic channel and its positivity
are independent premises.  A future physical Gram identification must produce
those premises on the same retained carrier.

## Axiom gate

Only finite products/lists, exact `Q'` arithmetic, and constructive `CReal`
limit operations are used.  There is no `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedConditionalLimitBridge

namespace YMGap.Continuum.BF4CompletedConditionalGramLimitBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompletedConditionalLimitBridge
open YMGap.Continuum.BF4CompletedProductLimitBridge
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack

/-! ## 1. Finite row/column entrywise amplification -/

/-- Turn explicit row/column coordinates into the single source coordinate
used by the conditional cutoff bridge. -/
def pairRetainedCoordinate
    {Row Column Target State Factor : Type}
    (coordinate :
      Row → Column → Target → List State → Factor → Q') :
    (Row × Column) → Target → List State → Factor → Q' :=
  fun source target path factor =>
    coordinate source.1 source.2 target path factor

/-- Literal rational matrix entry of the common-cutoff conditional kernel. -/
def pointwiseHeatCutoffConditionalMatrixEntry
    {Row Column Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w x :
      Row → Column → Target → List State → Factor → Q')
    (potential : State → Q')
    (row : Row) (column : Column) (target : Target)
    (cutoff : Nat) : Q' :=
  pointwiseHeatCutoffConditionalPathPushforward
    paths factors
    (pairRetainedCoordinate w)
    (pairRetainedCoordinate x)
    potential
    (row, column) target cutoff

/-- Completed matrix entry of the finite retained conditional kernel. -/
def completedPointwiseConditionalMatrixEntry
    {Row Column Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w x :
      Row → Column → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ row column target path factor,
        (0 : Q') ≤ w row column target path factor)
    (w_le_half :
      ∀ row column target path factor,
        w row column target path factor ≤ half)
    (x_lower :
      ∀ row column target path factor,
        (-(1 : Q')) ≤ x row column target path factor)
    (x_upper :
      ∀ row column target path factor,
        x row column target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (row : Row) (column : Column) (target : Target) : CReal :=
  completedConditionalPathPushforward
    paths
    (completedPointwiseRetainedKinetic
      factors
      (pairRetainedCoordinate w)
      (pairRetainedCoordinate x)
      (fun source target path factor =>
        w_nonnegative
          source.1 source.2 target path factor)
      (fun source target path factor =>
        w_le_half
          source.1 source.2 target path factor)
      (fun source target path factor =>
        x_lower
          source.1 source.2 target path factor)
      (fun source target path factor =>
        x_upper
          source.1 source.2 target path factor))
    potential
    (row, column) target

/-- Each row/column/target entry of the literal cutoff matrix converges to the
corresponding completed conditional entry. -/
theorem pointwiseHeatCutoffConditionalMatrixEntry_converges
    {Row Column Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w x :
      Row → Column → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ row column target path factor,
        (0 : Q') ≤ w row column target path factor)
    (w_le_half :
      ∀ row column target path factor,
        w row column target path factor ≤ half)
    (x_lower :
      ∀ row column target path factor,
        (-(1 : Q')) ≤ x row column target path factor)
    (x_upper :
      ∀ row column target path factor,
        x row column target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (row : Row) (column : Column) (target : Target) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pointwiseHeatCutoffConditionalMatrixEntry
            paths factors w x potential
            row column target cutoff))
      (completedPointwiseConditionalMatrixEntry
        paths factors w x
        w_nonnegative w_le_half x_lower x_upper
        potential row column target) := by
  unfold pointwiseHeatCutoffConditionalMatrixEntry
  unfold completedPointwiseConditionalMatrixEntry
  exact pointwiseHeatCutoffConditionalPathPushforward_converges
    paths factors
    (pairRetainedCoordinate w)
    (pairRetainedCoordinate x)
    (fun source target path factor =>
      w_nonnegative
        source.1 source.2 target path factor)
    (fun source target path factor =>
      w_le_half
        source.1 source.2 target path factor)
    (fun source target path factor =>
      x_lower
        source.1 source.2 target path factor)
    (fun source target path factor =>
      x_upper
        source.1 source.2 target path factor)
    potential potential_nonnegative
    (row, column) target

/-- Finite entrywise matrix amplification: cutoff removal holds at every
entry on supplied finite row, column, and target carriers. -/
theorem pointwiseHeatCutoffConditionalMatrix_finite_entrywise_converges
    {Row Column Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w x :
      Row → Column → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ row column target path factor,
        (0 : Q') ≤ w row column target path factor)
    (w_le_half :
      ∀ row column target path factor,
        w row column target path factor ≤ half)
    (x_lower :
      ∀ row column target path factor,
        (-(1 : Q')) ≤ x row column target path factor)
    (x_upper :
      ∀ row column target path factor,
        x row column target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (rows : List Row) (columns : List Column)
    (targets : List Target) :
    ∀ row, row ∈ rows →
      ∀ column, column ∈ columns →
        ∀ target, target ∈ targets →
          CReal.ConvergesTo
            (fun cutoff =>
              CReal.ofQ'
                (pointwiseHeatCutoffConditionalMatrixEntry
                  paths factors w x potential
                  row column target cutoff))
            (completedPointwiseConditionalMatrixEntry
              paths factors w x
              w_nonnegative w_le_half x_lower x_upper
              potential row column target) := by
  intro row _ column _ target _
  exact pointwiseHeatCutoffConditionalMatrixEntry_converges
    paths factors w x
    w_nonnegative w_le_half x_lower x_upper
    potential potential_nonnegative
    row column target

/-- The literal 23-factor version of finite entrywise matrix convergence. -/
theorem pointwiseHeatCutoffBF4ConditionalMatrix_finite_entrywise_converges
    {Row Column Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (_factor_count : factors.length = bf4SpatialCycleCount)
    (w x :
      Row → Column → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ row column target path factor,
        (0 : Q') ≤ w row column target path factor)
    (w_le_half :
      ∀ row column target path factor,
        w row column target path factor ≤ half)
    (x_lower :
      ∀ row column target path factor,
        (-(1 : Q')) ≤ x row column target path factor)
    (x_upper :
      ∀ row column target path factor,
        x row column target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (rows : List Row) (columns : List Column)
    (targets : List Target) :
    ∀ row, row ∈ rows →
      ∀ column, column ∈ columns →
        ∀ target, target ∈ targets →
          CReal.ConvergesTo
            (fun cutoff =>
              CReal.ofQ'
                (pointwiseHeatCutoffConditionalMatrixEntry
                  paths factors w x potential
                  row column target cutoff))
            (completedPointwiseConditionalMatrixEntry
              paths factors w x
              w_nonnegative w_le_half x_lower x_upper
              potential row column target) :=
  pointwiseHeatCutoffConditionalMatrix_finite_entrywise_converges
    paths factors w x
    w_nonnegative w_le_half x_lower x_upper
    potential potential_nonnegative
    rows columns targets

/-! ## 2. Already-formed weighted quadratic/Gram cutoff limits -/

/-- Literal rational finite-path weighted quadratic sum. -/
def rationalWeightedQuadraticPathSum
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (cutoffQuadratic : Path → Nat → Q')
    (cutoff : Nat) : Q' :=
  rationalPathSum
    (fun path =>
      pathWeight path * cutoffQuadratic path cutoff)
    paths

/-- Completed finite-path weighted quadratic sum. -/
def completedWeightedQuadraticPathSum
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (completedQuadratic : Path → CReal) : CReal :=
  completedPathSum
    (fun path =>
      CReal.mul
        (CReal.ofQ' (pathWeight path))
        (completedQuadratic path))
    paths

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ => value) value := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun approximation _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)

/-- One already-formed quadratic path channel remains convergent after
multiplication by its fixed nonnegative rational path weight. -/
theorem weightedQuadraticPath_converges
    {Path : Type}
    (pathWeight : Path → Q')
    (cutoffQuadratic : Path → Nat → Q')
    (completedQuadratic : Path → CReal)
    (path : Path)
    (pathWeight_nonnegative :
      (0 : Q') ≤ pathWeight path)
    (quadraticBound : Q')
    (quadraticBound_nonnegative :
      (0 : Q') ≤ quadraticBound)
    (quadraticLimitBound :
      ∀ approximation,
        Q'.abs ((completedQuadratic path).approx approximation) ≤
          quadraticBound)
    (quadraticConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.ofQ' (cutoffQuadratic path cutoff))
        (completedQuadratic path)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pathWeight path *
            cutoffQuadratic path cutoff))
      (CReal.mul
        (CReal.ofQ' (pathWeight path))
        (completedQuadratic path)) := by
  let commonBound : Q' :=
    Q'.max' (pathWeight path) quadraticBound
  have commonBound_nonnegative :
      (0 : Q') ≤ commonBound :=
    Q'.le_trans' _ _ _
      quadraticBound_nonnegative
      (Q'.le_max'_right
        (pathWeight path) quadraticBound)
  have scaleBound :
      ∀ cutoff approximation : Nat,
        Q'.abs
            ((CReal.ofQ' (pathWeight path)).approx approximation) ≤
          commonBound := by
    intro cutoff approximation
    change Q'.abs (pathWeight path) ≤ commonBound
    rw [ExpNeg.abs_of_nonneg
      pathWeight_nonnegative]
    exact Q'.le_max'_left
      (pathWeight path) quadraticBound
  have completedBound :
      ∀ approximation,
        Q'.abs ((completedQuadratic path).approx approximation) ≤
          commonBound := by
    intro approximation
    exact Q'.le_trans' _ _ _
      (quadraticLimitBound approximation)
      (Q'.le_max'_right
        (pathWeight path) quadraticBound)
  have multipliedConverges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.mul
            (CReal.ofQ' (pathWeight path))
            (CReal.ofQ'
              (cutoffQuadratic path cutoff)))
        (CReal.mul
          (CReal.ofQ' (pathWeight path))
          (completedQuadratic path)) :=
    CReal.convergesTo_mul
      commonBound_nonnegative
      scaleBound completedBound
      (convergesTo_const
        (CReal.ofQ' (pathWeight path)))
      quadraticConverges
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.mul
          (CReal.ofQ' (pathWeight path))
          (CReal.ofQ'
            (cutoffQuadratic path cutoff)))
  · intro cutoff
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul
        (pathWeight path)
        (cutoffQuadratic path cutoff))
  · exact multipliedConverges

/-- Common cutoff removal commutes with a finite sum of independently
supplied weighted quadratic/Gram path channels. -/
theorem rationalWeightedQuadraticPathSum_converges
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (cutoffQuadratic : Path → Nat → Q')
    (completedQuadratic : Path → CReal)
    (quadraticBound : Q')
    (quadraticBound_nonnegative :
      (0 : Q') ≤ quadraticBound)
    (quadraticLimitBound :
      ∀ path, path ∈ paths →
        ∀ approximation,
          Q'.abs ((completedQuadratic path).approx approximation) ≤
            quadraticBound)
    (quadraticConverges :
      ∀ path, path ∈ paths →
        CReal.ConvergesTo
          (fun cutoff =>
            CReal.ofQ' (cutoffQuadratic path cutoff))
          (completedQuadratic path)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (rationalWeightedQuadraticPathSum
            paths pathWeight cutoffQuadratic cutoff))
      (completedWeightedQuadraticPathSum
        paths pathWeight completedQuadratic) := by
  unfold rationalWeightedQuadraticPathSum
  unfold completedWeightedQuadraticPathSum
  apply rationalPathSum_converges
  intro path hpath
  exact weightedQuadraticPath_converges
    pathWeight cutoffQuadratic completedQuadratic
    path (pathWeight_nonnegative path hpath)
    quadraticBound quadraticBound_nonnegative
    (quadraticLimitBound path hpath)
    (quadraticConverges path hpath)

/-! ## 3. Positivity before and after cutoff removal -/

theorem rationalPathSum_nonnegative_on
    {Path : Type} (weight : Path → Q') :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        (0 : Q') ≤ weight path) →
      (0 : Q') ≤ rationalPathSum weight paths
  | [], _ => Q'.le_refl' 0
  | path :: tail, weight_nonnegative =>
      Q'.zero_le_add _ _
        (weight_nonnegative path List.mem_cons_self)
        (rationalPathSum_nonnegative_on
          weight tail
          (fun item hitem =>
            weight_nonnegative item
              (List.mem_cons_of_mem path hitem)))

/-- Every literal cutoff weighted quadratic sum is nonnegative when the
already-formed cutoff quadratic channels are nonnegative. -/
theorem rationalWeightedQuadraticPathSum_nonnegative
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (cutoffQuadratic : Path → Nat → Q')
    (cutoffQuadratic_nonnegative :
      ∀ path, path ∈ paths →
        ∀ cutoff,
          (0 : Q') ≤ cutoffQuadratic path cutoff)
    (cutoff : Nat) :
    (0 : Q') ≤
      rationalWeightedQuadraticPathSum
        paths pathWeight cutoffQuadratic cutoff := by
  unfold rationalWeightedQuadraticPathSum
  exact rationalPathSum_nonnegative_on
    (fun path =>
      pathWeight path * cutoffQuadratic path cutoff)
    paths
    (fun path hpath =>
      Q'.mul_nonneg _ _
        (pathWeight_nonnegative path hpath)
        (cutoffQuadratic_nonnegative
          path hpath cutoff))

/-- The completed weighted quadratic sum is nonnegative when the supplied
completed quadratic channels are nonnegative. -/
theorem completedWeightedQuadraticPathSum_nonnegative
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (completedQuadratic : Path → CReal)
    (completedQuadratic_nonnegative :
      ∀ path, path ∈ paths →
        ExpPos.geRat (completedQuadratic path) 0) :
    ExpPos.geRat
      (completedWeightedQuadraticPathSum
        paths pathWeight completedQuadratic)
      0 := by
  unfold completedWeightedQuadraticPathSum
  exact completedConditionalQuadratic_nonnegative
    paths pathWeight pathWeight_nonnegative
    completedQuadratic completedQuadratic_nonnegative

/-- Type-level certificate collecting cutoff positivity, cutoff convergence,
and positivity of the completed already-formed weighted quadratic channel. -/
structure WeightedQuadraticGramLimitCertificate
    (cutoffValue : Nat → Q') (completedValue : CReal) : Type where
  cutoffNonnegative :
    ∀ cutoff, (0 : Q') ≤ cutoffValue cutoff
  convergence :
    CReal.ConvergesTo
      (fun cutoff => CReal.ofQ' (cutoffValue cutoff))
      completedValue
  completedNonnegative :
    ExpPos.geRat completedValue 0

/-- Package the honest already-formed Gram premises into a single
witness-bearing cutoff-limit certificate. -/
def weightedQuadraticGramLimitCertificate
    {Path : Type}
    (paths : List Path)
    (pathWeight : Path → Q')
    (pathWeight_nonnegative :
      ∀ path, path ∈ paths →
        (0 : Q') ≤ pathWeight path)
    (cutoffQuadratic : Path → Nat → Q')
    (cutoffQuadratic_nonnegative :
      ∀ path, path ∈ paths →
        ∀ cutoff,
          (0 : Q') ≤ cutoffQuadratic path cutoff)
    (completedQuadratic : Path → CReal)
    (completedQuadratic_nonnegative :
      ∀ path, path ∈ paths →
        ExpPos.geRat (completedQuadratic path) 0)
    (quadraticBound : Q')
    (quadraticBound_nonnegative :
      (0 : Q') ≤ quadraticBound)
    (quadraticLimitBound :
      ∀ path, path ∈ paths →
        ∀ approximation,
          Q'.abs ((completedQuadratic path).approx approximation) ≤
            quadraticBound)
    (quadraticConverges :
      ∀ path, path ∈ paths →
        CReal.ConvergesTo
          (fun cutoff =>
            CReal.ofQ' (cutoffQuadratic path cutoff))
          (completedQuadratic path)) :
    WeightedQuadraticGramLimitCertificate
      (rationalWeightedQuadraticPathSum
        paths pathWeight cutoffQuadratic)
      (completedWeightedQuadraticPathSum
        paths pathWeight completedQuadratic) where
  cutoffNonnegative :=
    rationalWeightedQuadraticPathSum_nonnegative
      paths pathWeight pathWeight_nonnegative
      cutoffQuadratic cutoffQuadratic_nonnegative
  convergence :=
    rationalWeightedQuadraticPathSum_converges
      paths pathWeight pathWeight_nonnegative
      cutoffQuadratic completedQuadratic
      quadraticBound quadraticBound_nonnegative
      quadraticLimitBound quadraticConverges
  completedNonnegative :=
    completedWeightedQuadraticPathSum_nonnegative
      paths pathWeight pathWeight_nonnegative
      completedQuadratic completedQuadratic_nonnegative

end YMGap.Continuum.BF4CompletedConditionalGramLimitBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedConditionalGramLimitBridge.pointwiseHeatCutoffConditionalMatrix_finite_entrywise_converges
#print axioms YMGap.Continuum.BF4CompletedConditionalGramLimitBridge.pointwiseHeatCutoffBF4ConditionalMatrix_finite_entrywise_converges
#print axioms YMGap.Continuum.BF4CompletedConditionalGramLimitBridge.rationalWeightedQuadraticPathSum_converges
#print axioms YMGap.Continuum.BF4CompletedConditionalGramLimitBridge.weightedQuadraticGramLimitCertificate
