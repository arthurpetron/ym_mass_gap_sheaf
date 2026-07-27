/-
# Finite conditional integration commutes with the SU(2) cutoff limit

`BF4CompletedProductLimitBridge` proves convergence of the literal common
all-label cutoff product on a finite retained factor carrier.
`BF4CompletedRetainedConditionalOrder` defines the next physical operation:
multiply each retained path channel by its common nonnegative rational
interior-potential weight, then sum over a finite retained path list.

This module proves that the cutoff can be removed before or after that finite
conditional integration.  It supplies:

* a literal rational cutoff Feynman--Kac path weight;
* a literal rational finite-path pushforward;
* convergence of each weighted path channel;
* convergence of the full finite conditional pushforward to
  `completedConditionalPathPushforward`;
* the corresponding literal 23-factor BF4 retained-carrier statement.

Honest scope: the carrier, factor coordinates, paths, and potential are
supplied data.  No theorem here identifies this finite retained expression
with the interacting physical BF4 block kernel or with a continuum trajectory.

## Axiom gate

Only finite-list induction, exact `Q'` arithmetic, and constructive `CReal`
addition/multiplication continuity are used.  There is no `Classical.*`,
`Real`, `native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.BF4CompletedProductLimitBridge
import YMGap.Continuum.BF4CompletedRetainedConditionalOrder

namespace YMGap.Continuum.BF4CompletedConditionalLimitBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4CompletedHeatRetainedConsumer
open YMGap.Continuum.BF4CompletedProductLimitBridge
open YMGap.Continuum.BF4CompletedRetainedConditionalOrder
open YMGap.Continuum.BF4CompletedSU2PointwiseRetainedHarnack
open YMGap.Continuum.BF4GroupedFeynmanKacHarnack
open YMGap.Continuum.GroupedAllLabelHaarRefresh
open YMGap.Continuum.SU2AllLabelPointwiseHeatCompletion
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor

/-! ## 1. Literal rational finite-path pushforwards -/

/-- A finite sum of literal rational path weights. -/
def rationalPathSum {Path : Type}
    (weight : Path → Q') : List Path → Q'
  | [] => 0
  | path :: tail =>
      weight path + rationalPathSum weight tail

/-- The same finite rational path sum, with every summand embedded in
`CReal` before addition. -/
def liftedRationalPathSum {Path : Type}
    (weight : Path → Q') : List Path → CReal
  | [] => CReal.czero
  | path :: tail =>
      CReal.add
        (CReal.ofQ' (weight path))
        (liftedRationalPathSum weight tail)

@[simp] theorem liftedRationalPathSum_approx
    {Path : Type} (weight : Path → Q')
    (paths : List Path) (approximation : Nat) :
    (liftedRationalPathSum weight paths).approx approximation =
      rationalPathSum weight paths := by
  induction paths with
  | nil =>
      rfl
  | cons path tail ih =>
      change
        weight path +
            (liftedRationalPathSum weight tail).approx approximation =
          weight path + rationalPathSum weight tail
      rw [ih]

/-- Embedding after the literal finite rational sum is equivalent to embedding
each summand before the finite sum. -/
theorem ofQ'_rationalPathSum_equiv_lifted
    {Path : Type} (weight : Path → Q') (paths : List Path) :
    CReal.Equiv
      (CReal.ofQ' (rationalPathSum weight paths))
      (liftedRationalPathSum weight paths) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun approximation => by
      rw [liftedRationalPathSum_approx]
      exact Q'.eqv_refl _)

/-- The recursively lifted rational path sum is definitionally the existing
`completedPathSum` applied to rational embeddings, up to finite-list
unfolding. -/
theorem liftedRationalPathSum_eq_completedPathSum
    {Path : Type} (weight : Path → Q') :
    ∀ paths : List Path,
      liftedRationalPathSum weight paths =
        completedPathSum
          (fun path => CReal.ofQ' (weight path))
          paths
  | [] => rfl
  | path :: tail => by
      change
        CReal.add
            (CReal.ofQ' (weight path))
            (liftedRationalPathSum weight tail) =
          CReal.add
            (CReal.ofQ' (weight path))
            (completedPathSum
              (fun item => CReal.ofQ' (weight item))
              tail)
      rw [liftedRationalPathSum_eq_completedPathSum weight tail]

/-- Literal rational common-cutoff retained Feynman--Kac path weight. -/
def pointwiseHeatCutoffRetainedFeynmanKacWeight
    {Source Target State Factor : Type}
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (potential : State → Q')
    (source : Source) (target : Target)
    (path : List State) (cutoff : Nat) : Q' :=
  pathPotentialProduct potential path *
    pointwiseHeatCutoffRetainedKinetic
      factors w x source target path cutoff

/-- Literal rational common-cutoff conditional path pushforward. -/
def pointwiseHeatCutoffConditionalPathPushforward
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (potential : State → Q')
    (source : Source) (target : Target)
    (cutoff : Nat) : Q' :=
  rationalPathSum
    (fun path =>
      pointwiseHeatCutoffRetainedFeynmanKacWeight
        factors w x potential source target path cutoff)
    paths

/-! ## 2. Finite path sums preserve convergence -/

private theorem convergesTo_const (value : CReal) :
    CReal.ConvergesTo (fun _ => value) value := by
  intro ε hε
  refine ⟨0, fun _ _ => ⟨0, fun approximation _ => ⟨?_, ?_⟩⟩⟩
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)
  · exact Q'.add_le_self_of_nonneg
      (value.approx approximation) ε (Q'.le_of_lt hε)

/-- A finite list sum of convergent path channels converges to the finite list
sum of their limits. -/
theorem completedPathSum_converges
    {Path : Type}
    (sequence : Path → Nat → CReal)
    (limit : Path → CReal) :
    ∀ paths : List Path,
      (∀ path, path ∈ paths →
        CReal.ConvergesTo (sequence path) (limit path)) →
      CReal.ConvergesTo
        (fun cutoff =>
          completedPathSum
            (fun path => sequence path cutoff)
            paths)
        (completedPathSum limit paths)
  | [], _ =>
      convergesTo_const CReal.czero
  | path :: tail, path_converges => by
      exact
        YMGap.Constructive.TrigAddCReal.convergesTo_add
          (path_converges path List.mem_cons_self)
          (completedPathSum_converges
            sequence limit tail
            (fun item hitem =>
              path_converges item
                (List.mem_cons_of_mem path hitem)))

/-- The literal embedded rational finite path sums converge whenever the
embedded path weights converge. -/
theorem rationalPathSum_converges
    {Path : Type}
    (weight : Path → Nat → Q')
    (limit : Path → CReal)
    (paths : List Path)
    (path_converges :
      ∀ path, path ∈ paths →
        CReal.ConvergesTo
          (fun cutoff => CReal.ofQ' (weight path cutoff))
          (limit path)) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (rationalPathSum
            (fun path => weight path cutoff)
            paths))
      (completedPathSum limit paths) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        completedPathSum
          (fun path => CReal.ofQ' (weight path cutoff))
          paths)
  · intro cutoff
    rw [← liftedRationalPathSum_eq_completedPathSum
      (fun path => weight path cutoff) paths]
    exact CReal.Equiv.symm
      (ofQ'_rationalPathSum_equiv_lifted
        (fun path => weight path cutoff) paths)
  · exact completedPathSum_converges
      (fun path cutoff => CReal.ofQ' (weight path cutoff))
      limit paths path_converges

/-! ## 3. The weighted pathwise cutoff limit -/

private theorem completedPointwiseRetainedKinetic_abs_approx_le
    {Source Target State Factor : Type}
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (source : Source) (target : Target) (path : List State)
    (approximation : Nat) :
    Q'.abs
        ((completedPointwiseRetainedKinetic
          factors w x
          w_nonnegative w_le_half x_lower x_upper
          source target path).approx approximation) ≤
      finiteFactorBound allLabelHaarCeiling factors := by
  unfold completedPointwiseRetainedKinetic
  apply completedFactorProduct_abs_approx_le
    (bound_nonnegative :=
      Q'.le_of_lt allLabelHaarCeiling_pos)
  intro factor _ factorApproximation
  change
    Q'.abs
        (pointwiseHeatPartial
          (w source target path factor)
          (x source target path factor)
          factorApproximation) ≤
      allLabelHaarCeiling
  have partial_nonnegative :
      (0 : Q') ≤
        pointwiseHeatPartial
          (w source target path factor)
          (x source target path factor)
          factorApproximation :=
    Q'.le_trans' _ _ _
      (Q'.le_of_lt allLabelHaarFloor_pos)
      (allLabelHaarFloor_le_pointwiseHeatPartial
        (w_nonnegative source target path factor)
        (w_le_half source target path factor)
        (x_lower source target path factor)
        (x_upper source target path factor)
        factorApproximation)
  rw [ExpNeg.abs_of_nonneg partial_nonnegative]
  exact pointwiseHeatPartial_le_allLabelHaarCeiling
    (w_nonnegative source target path factor)
    (w_le_half source target path factor)
    (x_lower source target path factor)
    (x_upper source target path factor)
    factorApproximation

/-- Multiplication by the common nonnegative rational interior-potential
product preserves the cutoff limit of one retained path channel. -/
theorem pointwiseHeatCutoffRetainedFeynmanKacWeight_converges
    {Source Target State Factor : Type}
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (source : Source) (target : Target) (path : List State) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pointwiseHeatCutoffRetainedFeynmanKacWeight
            factors w x potential source target path cutoff))
      (completedRetainedFeynmanKacWeight
        (completedPointwiseRetainedKinetic
          factors w x
          w_nonnegative w_le_half x_lower x_upper)
        potential source target path) := by
  let potentialWeight : Q' :=
    pathPotentialProduct potential path
  let kineticBound : Q' :=
    finiteFactorBound allLabelHaarCeiling factors
  let commonBound : Q' :=
    Q'.max' potentialWeight kineticBound
  have potentialWeight_nonnegative :
      (0 : Q') ≤ potentialWeight :=
    pathPotentialProduct_nonnegative
      potential_nonnegative path
  have commonBound_nonnegative :
      (0 : Q') ≤ commonBound :=
    Q'.le_trans' _ _ _
      potentialWeight_nonnegative
      (Q'.le_max'_left potentialWeight kineticBound)
  have potential_sequence_bound :
      ∀ cutoff approximation : Nat,
        Q'.abs
            ((CReal.ofQ' potentialWeight).approx approximation) ≤
          commonBound := by
    intro cutoff approximation
    change Q'.abs potentialWeight ≤ commonBound
    rw [ExpNeg.abs_of_nonneg potentialWeight_nonnegative]
    exact Q'.le_max'_left potentialWeight kineticBound
  have kinetic_limit_bound :
      ∀ approximation,
        Q'.abs
            ((completedPointwiseRetainedKinetic
              factors w x
              w_nonnegative w_le_half x_lower x_upper
              source target path).approx approximation) ≤
          commonBound := by
    intro approximation
    exact Q'.le_trans' _ _ _
      (completedPointwiseRetainedKinetic_abs_approx_le
        factors w x
        w_nonnegative w_le_half x_lower x_upper
        source target path approximation)
      (Q'.le_max'_right potentialWeight kineticBound)
  have multiplied_converges :
      CReal.ConvergesTo
        (fun cutoff =>
          CReal.mul
            (CReal.ofQ' potentialWeight)
            (CReal.ofQ'
              (pointwiseHeatCutoffRetainedKinetic
                factors w x source target path cutoff)))
        (CReal.mul
          (CReal.ofQ' potentialWeight)
          (completedPointwiseRetainedKinetic
            factors w x
            w_nonnegative w_le_half x_lower x_upper
            source target path)) := by
    exact CReal.convergesTo_mul
      commonBound_nonnegative
      potential_sequence_bound
      kinetic_limit_bound
      (convergesTo_const (CReal.ofQ' potentialWeight))
      (pointwiseHeatCutoffRetainedKinetic_converges
        factors w x
        w_nonnegative w_le_half x_lower x_upper
        source target path)
  unfold pointwiseHeatCutoffRetainedFeynmanKacWeight
  unfold completedRetainedFeynmanKacWeight
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s :=
      fun cutoff =>
        CReal.mul
          (CReal.ofQ' potentialWeight)
          (CReal.ofQ'
            (pointwiseHeatCutoffRetainedKinetic
              factors w x source target path cutoff)))
  · intro cutoff
    exact CReal.Equiv.symm
      (CRealAlg.ofQ'_mul
        potentialWeight
        (pointwiseHeatCutoffRetainedKinetic
          factors w x source target path cutoff))
  · exact multiplied_converges

/-! ## 4. Cutoff removal commutes with finite conditional integration -/

/-- The literal common-cutoff rational retained Feynman--Kac kernel converges
to the completed finite conditional path pushforward. -/
theorem pointwiseHeatCutoffConditionalPathPushforward_converges
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (w x : Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (source : Source) (target : Target) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pointwiseHeatCutoffConditionalPathPushforward
            paths factors w x potential
            source target cutoff))
      (completedConditionalPathPushforward
        paths
        (completedPointwiseRetainedKinetic
          factors w x
          w_nonnegative w_le_half x_lower x_upper)
        potential source target) := by
  unfold pointwiseHeatCutoffConditionalPathPushforward
  unfold completedConditionalPathPushforward
  apply rationalPathSum_converges
  intro path _
  exact pointwiseHeatCutoffRetainedFeynmanKacWeight_converges
    factors w x
    w_nonnegative w_le_half x_lower x_upper
    potential potential_nonnegative
    source target path

/-- The requested retained BF4 form: on a literal 23-factor carrier, cutoff
removal commutes with the finite retained-path conditional integration.  The
count hypothesis records the BF4 retained factor count; the convergence proof
itself requires only that the supplied lists are finite. -/
theorem pointwiseHeatCutoffBF4ConditionalPathPushforward_converges
    {Source Target State Factor : Type}
    (paths : List (List State))
    (factors : List Factor)
    (_factor_count : factors.length = bf4SpatialCycleCount)
    (w x : Source → Target → List State → Factor → Q')
    (w_nonnegative :
      ∀ source target path factor,
        (0 : Q') ≤ w source target path factor)
    (w_le_half :
      ∀ source target path factor,
        w source target path factor ≤ half)
    (x_lower :
      ∀ source target path factor,
        (-(1 : Q')) ≤ x source target path factor)
    (x_upper :
      ∀ source target path factor,
        x source target path factor ≤ (1 : Q'))
    (potential : State → Q')
    (potential_nonnegative :
      ∀ state, (0 : Q') ≤ potential state)
    (source : Source) (target : Target) :
    CReal.ConvergesTo
      (fun cutoff =>
        CReal.ofQ'
          (pointwiseHeatCutoffConditionalPathPushforward
            paths factors w x potential
            source target cutoff))
      (completedConditionalPathPushforward
        paths
        (completedPointwiseRetainedKinetic
          factors w x
          w_nonnegative w_le_half x_lower x_upper)
        potential source target) :=
  pointwiseHeatCutoffConditionalPathPushforward_converges
    paths factors w x
    w_nonnegative w_le_half x_lower x_upper
    potential potential_nonnegative
    source target

end YMGap.Continuum.BF4CompletedConditionalLimitBridge

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CompletedConditionalLimitBridge.rationalPathSum_converges
#print axioms YMGap.Continuum.BF4CompletedConditionalLimitBridge.pointwiseHeatCutoffRetainedFeynmanKacWeight_converges
#print axioms YMGap.Continuum.BF4CompletedConditionalLimitBridge.pointwiseHeatCutoffConditionalPathPushforward_converges
#print axioms YMGap.Continuum.BF4CompletedConditionalLimitBridge.pointwiseHeatCutoffBF4ConditionalPathPushforward_converges
