/-
# Original Wilson time increments after joint time/cutoff removal

The literal adjacent-time difference is a signed expression in the existing
Wilson algebra. Its finite original expectation is twice the already defined
normalized Dirichlet energy. The proved kinetic bound is uniform in external
time depth and has a computed cutoff error; hence the SAME existing joint
CReal limit inherits the bound with that error removed.

Nome and spatial width are fixed during each limit. Width-independent bounds
do not identify states at different widths, construct their spatial limit,
or give a lower centered norm. No continuum survival or mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.SU2FundamentalNomeDisplacement

namespace YMGap.Continuum.BF4WilsonAllNomeKineticIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CReal.InnerRegularity (scaleTolerance scaleTolerance_pos mul_scaleTolerance_le)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (jump)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonKineticIncrement
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (includeLoop_edges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonActivePadding (includedLoop_edges_active)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.SU2HeatFusionCutoffError (cutoffErrorCutoff)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit normalizedEnergy

/-- SAME fundamental loop, at offsets zero and one, with its signed difference. -/
def differenceExpression {width : Nat} (loop : SourceLoop width) : WindowExpression width :=
  .add (.loop 0 loop 1) (.smul (-1) (.loop 1 loop 1))

def squareExpression {width : Nat} (loop : SourceLoop width) : WindowExpression width :=
  .mul (differenceExpression loop) (differenceExpression loop)

theorem square_within {width : Nat} (loop : SourceLoop width) :
    Within 1 (squareExpression loop) := by
  change (0 ≤ 1 ∧ 1 ≤ 1) ∧ (0 ≤ 1 ∧ 1 ≤ 1)
  decide

private theorem neg_smul (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

theorem source_square_pin {width : Nat} (loop : SourceLoop width) :
    RatPolyCoeffEqv (sourcePolynomial (squareExpression loop))
      (polyMul (jump width (sourceCharacter width loop.edges 1))
        (jump width (sourceCharacter width loop.edges 1))) := by
  have h : RatPolyCoeffEqv (sourcePolynomial (differenceExpression loop))
      (jump width (sourceCharacter width loop.edges 1)) := by
    simp only [differenceExpression, sourcePolynomial, Nat.zero_mul, Nat.one_mul]
    exact (RatPolyCoeffEqv.refl _).add (neg_smul _)
  exact h.mul h

/-- The finite expression's expectation is the EXISTING energy, not a new law. -/
theorem finite_increment_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (stage depth : Nat) :
    originalWindowScalar hw0 hw1 1 (squareExpression loop) stage depth depth ≈
      (2 : Q') * normalizedEnergy hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) depth (sourceCharacter width loop.edges 1) :=
  Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 1 _ (square_within loop) stage depth depth)
    (Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) depth 1 depth (source_square_pin loop))
      (Q'.eqv_symm (normalizedEnergy_window hw0 hw1 _ width (Nat.le_add_right _ _) depth
        (sourceCharacter_supported width loop.edges 1))))

/-- Exact squared path-length cost, including the fundamental trace factor. -/
def lengthCost (L : Nat) : Q' := 4 * (Q'.ofNat L * Q'.ofNat L)

theorem lengthCost_nonnegative (L : Nat) : (0 : Q') ≤ lengthCost L :=
  Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _))

/-- Computed heat-stage threshold; it has no width or external-time parameter. -/
def incrementCutoffStage (w : Q') (L : Nat) (epsilon : Q') : Nat :=
  cutoffErrorCutoff w (scaleTolerance (lengthCost L) epsilon)

theorem finite_increment_eventual {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (stage depth : Nat)
    (hstage : incrementCutoffStage w loop.edges.length epsilon ≤ stage) :
    originalWindowScalar hw0 hw1 1 (squareExpression loop) stage depth depth ≤
      lengthCost loop.edges.length * (2 + -(coeffW w 1)) + epsilon := by
  let c := lengthCost loop.edges.length
  let delta := scaleTolerance c epsilon
  have hd : (0 : Q') < delta := scaleTolerance_pos c epsilon he
  have hK : cutoffErrorCutoff w delta ≤ headCutoff w+stage := by
    exact Nat.le_trans hstage (Nat.le_add_left _ _)
  have hb := wilson_energy_tolerance hw0 hw1 delta hd (headCutoff w+stage) width
    (Nat.le_add_right _ _) hK depth loop hactive
  have hsplit : c*((2 + -(coeffW w 1))+delta) ≈ c*(2 + -(coeffW w 1))+c*delta :=
    Q'.mul_add_eqv _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (finite_increment_pin hw0 hw1 loop stage depth))
    (Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.add_le_add_left _ _ _ (mul_scaleTolerance_le c epsilon (lengthCost_nonnegative _) he))))

/-- The previous joint CReal limit of the literal original squared difference. -/
def incrementLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) : CReal :=
  originalJointLimit hw0 hw1 1 (squareExpression loop) (square_within loop)

theorem joint_increment_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) : leEv (ofQ' 0) (incrementLimit hw0 hw1 loop) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (originalJoint_diagonal_converges hw0 hw1 1 _ (square_within loop))
  intro epsilon he
  refine ⟨0, fun stage _ => ?_⟩
  have h := Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
    (normalizedEnergy_nonnegative hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) stage
      (sourceCharacter_supported width loop.edges 1))
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (finite_increment_pin hw0 hw1 loop stage stage))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)))

/-- Both external time boundaries and the heat cutoff are removed. The
actual action/state is unchanged, and the cutoff error is exactly absent. -/
theorem joint_increment_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    leEv (incrementLimit hw0 hw1 loop)
      (ofQ' (lengthCost loop.edges.length * (2 + -(coeffW w 1)))) := by
  apply leEv_of_ofQ'_limit_le
    (originalJoint_diagonal_converges hw0 hw1 1 _ (square_within loop)) (convergesTo_const _)
  intro epsilon he
  exact ⟨incrementCutoffStage w loop.edges.length epsilon,
    fun stage hs => finite_increment_eventual hw0 hw1 loop hactive epsilon he stage stage hs⟩

/-- Every fixed literal source loop is covered at every strictly larger
width. These are separate original states, not an assumed spatial limit. -/
theorem padded_joint_increment_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (loop : SourceLoop base) :
    leEv (incrementLimit hw0 hw1
      (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop))
      (ofQ' (lengthCost loop.edges.length * (2 + -(coeffW w 1)))) := by
  have h := joint_increment_bound hw0 hw1
    (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop)
    (includedLoop_edges_active hwidth loop)
  rw [includeLoop_edges (Nat.le_of_lt hwidth) loop] at h
  exact h

/-- Explicit endpoint-linear nome budget for the SAME joint limiting state. -/
theorem joint_increment_nome_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges → (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    leEv (incrementLimit hw0 hw1 loop)
      (ofQ' (24 * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) * (1 + -w))) :=
  leEv_trans (joint_increment_bound hw0 hw1 loop hactive)
    (leEv_ofQ'_of_approx_ge (fun _ =>
      SU2FundamentalNomeDisplacement.scaled_displacement_le
        (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) loop.edges.length))

/-- No ambient-width or exterior-time factor is introduced by taking the
existing joint limit. The source word and its length are fixed. -/
theorem padded_joint_increment_nome_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (loop : SourceLoop base) :
    leEv (incrementLimit hw0 hw1
      (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop))
      (ofQ' (24 * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) * (1 + -w))) := by
  have h := joint_increment_nome_bound hw0 hw1
    (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop)
    (includedLoop_edges_active hwidth loop)
  rw [includeLoop_edges (Nat.le_of_lt hwidth) loop] at h
  exact h

/-- Positive rational nome-defect tolerance as DATA. It depends only on the
literal path length and the requested squared-increment tolerance. -/
def nomeTolerance (L : Nat) (epsilon : Q') : Q' :=
  scaleTolerance (24 * (Q'.ofNat L * Q'.ofNat L)) epsilon

theorem nomeTolerance_positive (L : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) :
    (0 : Q') < nomeTolerance L epsilon := scaleTolerance_pos _ epsilon he

/-- Uniform smallness of ADJACENT-LATTICE-TIME squared increments as w tends
to one. No spacing, fixed physical-time interval, or surviving norm is asserted. -/
theorem padded_joint_increment_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width) (loop : SourceLoop base)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (hw : 1 + -w ≤ nomeTolerance loop.edges.length epsilon) :
    leEv (incrementLimit hw0 hw1
      (recenterLoop (space := 0) (by omega : base+0 ≤ width) loop)) (ofQ' epsilon) := by
  have hc : (0 : Q') ≤ 24 * (Q'.ofNat loop.edges.length * Q'.ofNat loop.edges.length) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _))
  exact leEv_trans (padded_joint_increment_nome_bound hw0 hw1 hwidth loop)
    (leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hw hc)
      (mul_scaleTolerance_le _ epsilon hc he)))

end YMGap.Continuum.BF4WilsonAllNomeKineticIncrement

#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.differenceExpression
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.squareExpression
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.square_within
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.source_square_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.finite_increment_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.lengthCost
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.lengthCost_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.incrementCutoffStage
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.finite_increment_eventual
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.incrementLimit
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.joint_increment_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.joint_increment_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.padded_joint_increment_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.joint_increment_nome_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.padded_joint_increment_nome_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.nomeTolerance
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.nomeTolerance_positive
#print axioms YMGap.Continuum.BF4WilsonAllNomeKineticIncrement.padded_joint_increment_small
