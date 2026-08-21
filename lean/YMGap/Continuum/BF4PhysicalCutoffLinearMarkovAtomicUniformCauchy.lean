/-
# Uniform pointwise compiler for atomic physical BF4 Markov Cauchy data

The remaining pointwise-data residual has already been reduced from arbitrary
finite-linear syntax to atomic physical `[0,1]` observables.  This file exposes
the finite estimate that is sufficient for each such atom.

If two cutoff-recoded atomic Markov images have pointwise squared difference
at most `epsilon` on every edge labelling, then their squared distance in the
cutoff-removed physical GNS form is at most `epsilon`.  The proof checks every
finite approximation: positivity of the stationary row marginal permits
termwise comparison, and its exact total mass one removes the average.

Consequently a uniform pointwise squared Cauchy modulus for every atom
constructs `CentralPhysicalLinearMarkovAtomicCauchyData`, and hence the full
pointwise datum consumed by the adaptive completed-transfer chain.

No uniform nonconstant kernel modulus is inhabited here.  The analytic
residual is now a finite rational pointwise estimate, rather than a statement
inside a completion or quotient.

## Axiom gate

Only finite list monotonicity, nonnegative normalized BF4 row marginals, exact
rational algebra, and the already proved finite-stage GNS bridge are used.
There is no classical choice, noncomputable declaration, custom axiom, or
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A normalized finite average preserves pointwise square bounds -/

private theorem leEv_of_approx_le {left right : CReal}
    (h : forall cutoff, left.approx cutoff <= right.approx cutoff) :
    CReal.leEv left right := by
  intro epsilon hepsilon
  exact ⟨0, fun cutoff _ =>
    Q'.le_trans' _ _ _ (h cutoff)
      (Q'.add_le_self_of_nonneg
        (right.approx cutoff) epsilon (Q'.le_of_lt hepsilon))⟩

private theorem weighted_pointwise_square_le
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (left right : EdgeLabelling -> Q') (epsilon : Q')
    (hbound : forall state,
      let difference := left state + -(right state)
      difference * difference <= epsilon) :
    (centralPhysicalSmulGNS w hw cutoff half).toGNSData.distSqQ
        left right <= epsilon := by
  let D := (centralPhysicalSmulGNS w hw cutoff half).toGNSData
  let states := centralPositiveHalfStates w hw cutoff half
  let row := centralPhysicalRowMarginal w hw cutoff half
  change centralPhysicalWeightedInner w hw cutoff half
      (D.sub left right) (D.sub left right) <= epsilon
  unfold centralPhysicalWeightedInner
  refine Q'.le_trans' _ (listQSum (fun state => row state * epsilon) states) _ ?_ ?_
  · apply listQSum_mono
    intro state _
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (hbound state)
      (centralPhysicalRowMarginal_nonnegative hw cutoff half state)
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ (listQSum row states * epsilon) _
        (listQSum_mul_right row epsilon states)
        (Q'.eqv_trans _ ((1 : Q') * epsilon) _
          (Q'.mul_eqv_congr_right _ _ epsilon
            (centralPositiveRowMarginal_total_one w hw cutoff half))
          (Q'.one_mul_eqv epsilon)))

/-- A global pointwise squared bound on two finite-linear observables bounds
their squared distance in the cutoff-removed physical GNS form. -/
theorem physicalLinearDistSq_le_of_pointwise_sq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable)
    (epsilon : Q')
    (hbound : forall state,
      let difference := left.value state + -(right.value state)
      difference * difference <= epsilon) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half left right)
      (CReal.ofQ' epsilon) := by
  apply leEv_of_approx_le
  intro cutoff
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (physicalLinearDistSq_approx_eqv_stage
        hw0 hw1 half cutoff left right))
    (weighted_pointwise_square_le
      (Q'.le_of_lt hw0) cutoff half left.value right.value epsilon hbound)

/-! ## 2. The finite pointwise atomic residual -/

/-- A uniform squared Cauchy modulus for the globally recoded atomic Markov
images.  Every field is a finite rational statement on edge labellings. -/
structure CentralPhysicalAtomicMarkovUniformSqCauchyData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  rate :
    YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable ->
      Q' -> Nat
  pointwiseSq : forall
    (observable :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (epsilon : Q'), (0 : Q') < epsilon ->
    forall m n, rate observable epsilon <= m -> rate observable epsilon <= n ->
    forall state,
      let left := centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) m half (atom observable)
      let right := centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) n half (atom observable)
      let difference := left.value state + -(right.value state)
      difference * difference <= epsilon

/-! ## 3. Handoff to atomic and dense Cauchy data -/

/-- Uniform pointwise atomic convergence supplies the atomic GNS-distance
moduli required by the finite-linear compiler. -/
def CentralPhysicalAtomicMarkovUniformSqCauchyData.toAtomicCauchyData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (uniform : CentralPhysicalAtomicMarkovUniformSqCauchyData
      hw0 hw1 half) :
    CentralPhysicalLinearMarkovAtomicCauchyData hw0 hw1 half where
  modulus observable :=
    { rate := uniform.rate observable
      cauchy := by
        intro epsilon hepsilon m n hm hn
        exact physicalLinearDistSq_le_of_pointwise_sq
          hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) m half (atom observable))
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) n half (atom observable))
          epsilon
          (uniform.pointwiseSq observable epsilon hepsilon m n hm hn) }

/-- Uniform pointwise atomic convergence therefore constructs the exact dense
Cauchy datum consumed by the adaptive completed-transfer chain. -/
def CentralPhysicalAtomicMarkovUniformSqCauchyData.toDenseCauchyData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (uniform : CentralPhysicalAtomicMarkovUniformSqCauchyData
      hw0 hw1 half) :
    CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half :=
  uniform.toAtomicCauchyData.toDenseCauchyData

/-! ## Axiom audit -/

#print axioms physicalLinearDistSq_le_of_pointwise_sq
#print axioms CentralPhysicalAtomicMarkovUniformSqCauchyData
#print axioms CentralPhysicalAtomicMarkovUniformSqCauchyData.toAtomicCauchyData
#print axioms CentralPhysicalAtomicMarkovUniformSqCauchyData.toDenseCauchyData

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy
