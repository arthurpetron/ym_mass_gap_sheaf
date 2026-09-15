/-
# The explicit continuous filter is the ORIGINAL unit projection

For h(t)=clip(4t-3), the support inequality forces
  (3/4)||h(T2)x||^2 <= <T2 h(T2)x,h(T2)x>.
The existing unit-complement gap bounds the right side by
(1/2)||h(T2)x||^2 for centered x. Thus h(T2) annihilates that same
complement. Evaluation at one fixes the original unit, and symmetry
fixes its original projection. The original center decomposition proves
h(T2)=unitProjection on EVERY original completed state.

The Bernstein representative/rate certificate is pinned to that same
projection. No spectral resolution, projection, density or physical gap
is supplied. This is fixed SU(2) nome 1/1024 and fixed lattice spacing;
time injectivity, continuous time, physical scaling and continuum/Clay
remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef (completedInner_posdef)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus
open YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol (productSymbol productVanishing)
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolAlgebra (scaledSymbol scaledVanishing)
open YMGap.Continuum.BF4ExactSlabThermodynamicClippedSymbols
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnit
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local notation "F" => unitFilterSymbol
local notation "V" => unitFilterVanishing
local notation "u" => completedUnit
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)
local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem zero_of_edge_half (a : RC) (ha : RCnonneg a)
    (h : RCle (RCscale filterEdge a) (RCscale HalfPow.half a)) : a=RCzero := by
  revert ha h
  refine Quotient.inductionOn a ?_
  intro A ha h
  apply RCle_antisymm ?_ ha
  intro epsilon he
  let e := Q'.divPos epsilon 4 (by decide)
  have he' : (0 : Q')<e := Q'.divPos_pos _ _ _ he
  obtain ⟨N,hN⟩ := h e he'
  refine ⟨N,fun n hn => ?_⟩
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ 4 (hN n hn) (by decide)
  have hl : Q'.eqv (4*(filterEdge*A.approx n)) (A.approx n+2*A.approx n) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ 3 _ (by decide))
        (poly_identity_of_normal_eq (.mul (.const 3) (.var 0))
          (.add (.var 0) (.mul (.const 2) (.var 0))) (by decide) (fun _ => A.approx n)))
  have hhalf : Q'.eqv (4*(HalfPow.half*A.approx n)) (2*A.approx n) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ 2 _ (by decide))
  have heq : Q'.eqv (4*e) epsilon :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.divPos_mul_eqv epsilon 4 (by decide))
  have hr : Q'.eqv (4*(HalfPow.half*A.approx n+e)) (epsilon+2*A.approx n) :=
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hhalf heq) (Q'.add_comm_eqv _ _))
  have hx : A.approx n≤epsilon := le_of_add_le_add_right
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl) (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hr)))
  simpa only [czero,ofQ',Q'.zero_add'] using hx

theorem unitFilter_support_form (x : Completion) :
    RCle (RCscale filterEdge (completedInner (continuousAction F V x) (continuousAction F V x)))
      (completedInner (twoStepTransfer (continuousAction F V x)) (continuousAction F V x)) := by
  have hp : ∀ t : Q',(0 : Q')≤t → t≤1 →
      (scaledSymbol filterEdge (productSymbol F V F V) (productVanishing F V F V)).f t≤
        (productSymbol F V (productSymbol coordinateSymbol coordinateVanishing F V)
          (productVanishing coordinateSymbol coordinateVanishing F V)).f t := by
    intro t ht h1
    change filterEdge*(unitFilterSymbol.f t*unitFilterSymbol.f t)≤
      unitFilterSymbol.f t*(coordinateSymbol.f t*unitFilterSymbol.f t)
    rw [coordinate_value t ht h1]
    exact Q'.le_trans' _ _ _ (unitFilter_support t)
      (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 1) (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => t | _ => unitFilterSymbol.f t)))
  have hb := continuousAction_form_mono _ (scaledVanishing filterEdge _ (productVanishing F V F V))
    _ (productVanishing F V _ (productVanishing coordinateSymbol coordinateVanishing F V)) hp x
  rw [scaledSymbol_action,completedInner_smul_left,productSquare_form_identity,
    productSymbol_pairing,productSymbol_composition,coordinate_action] at hb
  exact hb

theorem unitFilter_complement_zero (x : UnitComplement) : continuousAction F V x.val=completedZero := by
  have hs := unitFilter_support_form x.val
  have hg := complementAction_twoStep_form_gap F V x
  change RCle (completedInner (continuousAction F V x.val) (twoStepTransfer (continuousAction F V x.val))) _ at hg
  rw [completedInner_symm (continuousAction F V x.val) (twoStepTransfer (continuousAction F V x.val))] at hg
  exact (completedInner_posdef _).mp (zero_of_edge_half _ (completedInner_nonnegative _) (RCle_trans hs hg))

theorem unitFilter_center_zero (x : Completion) : continuousAction F V (center x)=completedZero :=
  unitFilter_complement_zero (centeredState x)

theorem unitFilter_unit : continuousAction F V u=u := by
  rw [continuousAction_unit]
  exact (completedSmul_congr unitFilter_at_one u).trans (completedSmul_one u)

theorem unitFilter_projection (x : Completion) : continuousAction F V (unitProjection x)=unitProjection x := by
  apply completed_eq_of_pairings
  intro y
  rw [continuousAction_symmetric,unitProjection_pairing,← continuousAction_symmetric,
    unitFilter_unit,unitProjection_pairing]

/-- The explicit continuous filter equals the pre-existing ORIGINAL projection on every state. -/
theorem unitFilter_eq_projection (x : Completion) : continuousAction F V x=unitProjection x := by
  calc
    continuousAction F V x=continuousAction F V (completedAdd (center x) (unitProjection x)) :=
      congrArg (continuousAction F V) (center_decomposition x).symm
    _=completedAdd (continuousAction F V (center x)) (continuousAction F V (unitProjection x)) :=
      continuousAction_add F V _ _
    _=unitProjection x := by rw [unitFilter_center_zero,unitFilter_projection,completedZero_add]

theorem unitFilter_idempotent (x : Completion) :
    continuousAction F V (continuousAction F V x)=continuousAction F V x := by
  simp only [unitFilter_eq_projection,unitProjection_idempotent]

theorem unitFilter_nonzero : continuousAction F V u≠completedZero := by
  rw [unitFilter_unit]
  exact completedUnit_ne_zero

/-- Explicit Bernstein output data, with its equality to the SAME original projection. -/
def unitProjectionFilterCertificate (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy,
      {rate : Q' → Nat // (point Y)=unitProjection (point X) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (completedDist (polynomialOperator (bernsteinPoly F n) (point X)) (point Y)) (rat epsilon)} :=
  ⟨actionRepresentative F V X,⟨actionModulus F V X,
    (actionRepresentative_pin F V X).trans (unitFilter_eq_projection _),continuousAction_bound F V X⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.zero_of_edge_half
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_support_form
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_complement_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_center_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_projection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_eq_projection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_idempotent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitFilter_nonzero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousUnitProjection.unitProjectionFilterCertificate
