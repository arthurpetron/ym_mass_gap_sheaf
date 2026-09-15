/-
# Closed maximal derivative graph in the ORIGINAL real pairing

The equation J u = T2 v is equivalent to the adjoint test against the
OLD differentiated dense domain. Constructed two-coordinate approximants
prove symmetry and positivity of this whole graph. The equation is closed
under supplied original Cauchy rows. Testing against the whole graph is
then equivalent to the same equation: an actual real-pairing adjoint-graph
equality, not a maximality or self-adjointness assumption.

The centered form bound >=1/2 passes through the SAME graph approximants.
The graph is single-valued by the original T2 injectivity, and its dense
domain already contains the old T2 range with explicit approximations.
No inverse, quotient representative selection or replacement Hilbert
carrier is introduced. Row limits retain the original data/moduli.
Every graph image is orthogonal to the constructed unit vacuum. The
centered zero-image kernel is trivial by the same form gap and definiteness.

Whole-graph differentiation is proved downstream in GraphRealDerivative.
The canonical physical Hamiltonian interface and spectral interpretation, physical time/spacing/
beta(a), continuum QFT and all gauge groups remain open. This is the
original real completion at SU(2), nome 1/1024 and fixed spacing, with
T2-time units; it is not a continuum or Clay mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef (completedInner_posdef)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialRowAction (operatorRows operatorRows_pin operator_rowLimit)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator (operator_constant)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolvent (defect)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments (defectPower)
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation (partialPreimage partialPreimageCauchy partialPreimageCauchy_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative (derivativeRepresentative derivativeRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws
open YMGap.Continuum.BF4ExactSlabThermodynamicLogarithmicCore (CorePoint)
open YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore (image image_nonnegative image_form_gap)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X

def GraphPoint.add (p q : GraphPoint) : GraphPoint where
  state := completedAdd p.state q.state
  image := completedAdd p.image q.image
  equation := by rw [derivative_add,p.equation,q.equation]; exact (completedTime_add 2 _ _).symm

def GraphPoint.realSmul (s : CReal) (cs : QCauchy s.approx) (p : GraphPoint) : GraphPoint where
  state := completedRealSmul s cs p.state
  image := completedRealSmul s cs p.image
  equation := by rw [derivative_realSmul,p.equation]; exact (completedTime_realSmul 2 s cs _).symm

def vacuum : GraphPoint where
  state := completedUnit
  image := completedZero
  equation := by rw [derivative_unit]; exact (completedTime_zeroState 2).symm

/-- The old constructive domain-density witness now lands in the actual graph. -/
def denseGraphData (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' p : GraphPoint, RCle (completedDist (point X) p.state) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
  ⟨fromCore (BF4ExactSlabThermodynamicLogarithmicCore.coreApproximation X epsilon),
    BF4ExactSlabThermodynamicLogarithmicCore.coreApproximation_bound X epsilon he⟩

theorem core_test (p : GraphPoint) (q : CorePoint) : B p.image q.state=B p.state (image q) := by
  change B p.image (twoStepTransfer q.preimage)=B p.state (derivativeAction q.preimage)
  rw [← twoStepTransfer_symmetric,← derivative_symmetric,p.equation]

/-- The whole proposed graph is exactly the adjoint test against the original dense domain. -/
theorem core_test_iff (u v : Completion) :
    (∀ q : CorePoint,B v q.state=B u (image q)) ↔ derivativeAction u=twoStepTransfer v := by
  constructor
  · intro h
    apply completed_eq_of_pairings
    intro z
    have hz := h ⟨z⟩
    change B v (twoStepTransfer z)=B u (derivativeAction z) at hz
    rw [← twoStepTransfer_symmetric,← derivative_symmetric] at hz
    exact hz.symm
  · intro h q
    exact core_test ⟨u,v,h⟩ q

/-- The defining equation survives actual constructed original row limits. -/
theorem graph_closed (R S : CauchyRows)
    (h : ∀ n,derivativeAction (rowPoint R n)=twoStepTransfer (rowPoint S n)) :
    derivativeAction (rowLimit R)=twoStepTransfer (rowLimit S) := by
  apply completed_eq_of_pairings
  intro z
  rw [derivative_symmetric,twoStepTransfer_symmetric]
  refine Quotient.inductionOn z ?_
  intro Z
  have hb := rowLimit_pairing_eq R (constantRows (derivativeRepresentative Z)) S (constantRows (timeCauchy 2 Z)) (by
    intro n
    rw [constantRows_pin,constantRows_pin,derivativeRepresentative_pin]
    change B (rowPoint R n) (derivativeAction (point Z))=B (rowPoint S n) (twoStepTransfer (point Z))
    rw [← derivative_symmetric,← twoStepTransfer_symmetric,h n])
  rw [rowLimit_constant,rowLimit_constant,derivativeRepresentative_pin] at hb
  exact hb

def graphRowLimit (R S : CauchyRows)
    (h : ∀ n,derivativeAction (rowPoint R n)=twoStepTransfer (rowPoint S n)) : GraphPoint :=
  ⟨rowLimit R,rowLimit S,graph_closed R S h⟩

/-- Constructed domain approximants, not adjoint symmetry assumed as a field. -/
theorem GraphPoint.symmetric (p q : GraphPoint) : B p.image q.state=B p.state q.image := by
  rcases p with ⟨u,v,hu⟩
  rcases q with ⟨w,z,hw⟩
  change B v w=B u z
  revert hu hw
  refine Quotient.inductionOn₂ u v ?_
  intro U V hu
  refine Quotient.inductionOn₂ w z ?_
  intro W Z hw
  have h := rowLimit_pairing_eq (imageRows U V hu) (constantRows W) (stateRows U V) (constantRows Z) (by
    intro n
    rw [imageRows_pin,stateRows_pin,constantRows_pin,constantRows_pin,
      completedInner_symm (image (approximant U V (half^n))) (point W),
      completedInner_symm (approximant U V (half^n)).state (point Z)]
    exact (core_test ⟨point W,point Z,hw⟩ (approximant U V (half^n))).symm)
  rw [imageRows_limit,stateRows_limit,rowLimit_constant,rowLimit_constant] at h
  exact h

/-- The actual graph image is orthogonal to the original unit vacuum. -/
theorem GraphPoint.image_orthogonal_unit (p : GraphPoint) : B p.image completedUnit=RCzero := by
  have h := GraphPoint.symmetric p vacuum
  change B p.image completedUnit=B p.state completedZero at h
  rw [completedInner_zero_right] at h
  exact h

/-- Equality with its REAL-PAIRING adjoint graph, on the same original completion. -/
theorem selfAdjoint_graph_iff (u v : Completion) :
    (∀ p : GraphPoint,B v p.state=B u p.image) ↔ derivativeAction u=twoStepTransfer v := by
  constructor
  · intro h
    exact (core_test_iff u v).mp (fun q => h (fromCore q))
  · intro h p
    exact GraphPoint.symmetric ⟨u,v,h⟩ p

theorem GraphPoint.nonnegative (p : GraphPoint) : RCnonneg (B p.image p.state) := by
  rcases p with ⟨u,v,hp⟩
  change RCnonneg (B v u)
  revert hp
  refine Quotient.inductionOn₂ u v ?_
  intro U V hp
  have h := rowLimit_pairing_nonnegative (imageRows U V hp) (stateRows U V) (by
    intro n
    rw [imageRows_pin,stateRows_pin]
    exact image_nonnegative _)
  rw [imageRows_limit,stateRows_limit] at h
  exact h

private theorem defectPower_orthogonal (n : Nat) (x : Completion) (hx : B x completedUnit=RCzero) :
    B (defectPower n x) completedUnit=RCzero := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      change B (completedSub (defectPower n x) (completedTime 2 (defectPower n x))) completedUnit=RCzero
      rw [completedInner_sub_left,completedTime_mean,ih]
      exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
        (by decide : Q'.eqv ((0 : Q') + -0) 0)))

theorem partialPreimage_orthogonal (n : Nat) (x : Completion) (hx : B x completedUnit=RCzero) :
    B (partialPreimage n x) completedUnit=RCzero := by
  induction n with
  | zero => exact completedInner_zero_left _
  | succ n ih => rw [partialPreimage,completedInner_add_left,ih,defectPower_orthogonal n x hx,rc_add_zero]

theorem approximant_orthogonal (U V : seminorm.Cauchy) (hU : B (point U) completedUnit=RCzero) (epsilon : Q') :
    B (approximant U V epsilon).state completedUnit=RCzero := by
  change B (completedTime 2 (point (partialPreimageCauchy (graphDegree U V epsilon) U))) completedUnit=RCzero
  rw [completedTime_mean,partialPreimageCauchy_pin]
  exact partialPreimage_orthogonal _ _ hU

/-- The original dense-domain form gap extends through the constructed graph approximations. -/
theorem GraphPoint.form_gap (p : GraphPoint) (hc : B p.state completedUnit=RCzero) :
    RCle (RCscale half (B p.state p.state)) (B p.image p.state) := by
  rcases p with ⟨u,v,hp⟩
  change RCle (RCscale half (B u u)) (B v u)
  change B u completedUnit=RCzero at hc
  revert hp hc
  refine Quotient.inductionOn₂ u v ?_
  intro U V hp hc
  have h := rowLimit_pairing_le (operatorRows [half] (stateRows U V)) (stateRows U V)
    (imageRows U V hp) (stateRows U V) (by
      intro n
      rw [operatorRows_pin,operator_constant,stateRows_pin,imageRows_pin,completedInner_smul_left]
      exact image_form_gap _ (approximant_orthogonal U V hc (half^n)))
  rw [operator_rowLimit,operator_constant,stateRows_limit,imageRows_limit,completedInner_smul_left] at h
  exact h

/-- No nonzero centered state in the ORIGINAL graph has zero image.
This is a graph-kernel statement in T2-time units, not a physical spectral theorem. -/
theorem GraphPoint.centered_kernel_trivial (p : GraphPoint)
    (hc : B p.state completedUnit=RCzero) (hv : p.image=completedZero) :
    p.state=completedZero := by
  apply (completedInner_posdef p.state).mp
  have hg := GraphPoint.form_gap p hc
  rw [hv,completedInner_zero_left] at hg
  have h := RCscale_mono (by decide : (0 : Q')≤2) hg
  rw [RCscale_RCscale,scale_congr (by decide : Q'.eqv ((2 : Q')*half) 1),
    RCscale_one,RCscale_RCzero] at h
  exact RCle_antisymm h (completedInner_nonnegative p.state)

end YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.vacuum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.denseGraphData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.core_test
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.core_test_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.graph_closed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.graphRowLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.image_orthogonal_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.selfAdjoint_graph_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.partialPreimage_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.approximant_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.form_gap
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph.GraphPoint.centered_kernel_trivial
