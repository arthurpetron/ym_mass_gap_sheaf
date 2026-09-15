/-
# The original unit complement is invariant under continuous calculus

Centering commutes with the original polynomial action and with its
constructed continuous limits. Consequently the full-carrier calculus
restricts to an actual operator on the existing UnitComplement type.
Products, symmetry, positivity and the sharp norm bound remain on that
SAME sector. The previously proved fixed-spacing two-step form gap
therefore applies to the filtered vectors, with no new gap hypothesis.

This does not prove injectivity of the transfer, construct continuous time
or identify a physical-scale Hamiltonian. The fixed SU(2) nome/spacing,
continuum and Clay boundaries are unchanged.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder
import YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredDensity
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGap (complement_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicProductSymbol (productSymbol productVanishing)
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorContinuousLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorMultiplication
open YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorSymbolOrder

local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem center_smul (c : Q') (x : Completion) :
    center (completedSmul c x)=completedSmul c (center x) := by
  apply completed_eq_of_pairings
  intro y
  rw [center_selfAdjoint,completedInner_smul_left,completedInner_smul_left,center_selfAdjoint]

theorem center_polynomialVector (x : Completion) (p : QPoly.Poly) (r : Nat) :
    center (polynomialVector x p r)=polynomialVector (center x) p r := by
  induction p generalizing r with
  | nil => exact center_zero
  | cons c p ih =>
      rw [polynomialVector,polynomialVector,center_add,center_smul,← completedTime_center,ih]

/-- Centering is the SAME original projection complement on both sides. -/
theorem continuousAction_center (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : Completion) :
    continuousAction F V (center x)=center (continuousAction F V x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h : representedAction F V (centerCauchy X)=rowLimit (centeredRows (symbolRows F V X)) := by
    apply rowLimit_independent
    intro n
    rw [symbolRows_pin,centeredRows_rowPoint,symbolRows_pin]
    exact (center_polynomialVector (point X) (bernsteinPoly F n) 0).symm
  exact h.trans (rowLimit_centeredRows _)

theorem continuousAction_orthogonal (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (x : Completion) (hx : completedInner x completedUnit=RCzero) :
    completedInner (continuousAction F V x) completedUnit=RCzero := by
  apply (center_fixed_iff _).mp
  rw [← continuousAction_center,(center_fixed_iff x).mpr hx]

/-- Constructed restriction, not a separately chosen model of the unit complement. -/
def complementAction (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : UnitComplement) : UnitComplement :=
  ⟨continuousAction F V x.val,continuousAction_orthogonal F V x.val x.property⟩

theorem complementAction_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : UnitComplement) :
    (complementAction F V x).val=continuousAction F V x.val := rfl

theorem complementAction_product (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (x : UnitComplement) :
    complementAction (productSymbol F V G W) (productVanishing F V G W) x=
      complementAction F V (complementAction G W x) := by
  apply Subtype.ext
  exact productSymbol_composition F V G W x.val

theorem complementAction_symmetric (F : CtsMod) (V : MonotoneOmegaVanishing F) (x y : UnitComplement) :
    completedInner (complementAction F V x).val y.val=completedInner x.val (complementAction F V y).val :=
  continuousAction_symmetric F V x.val y.val

theorem complementAction_nonnegative (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (hF : ∀ t : Q',(0 : Q')≤t → t≤1 → (0 : Q')≤F.f t) (x : UnitComplement) :
    RCnonneg (completedInner (complementAction F V x).val x.val) :=
  continuousAction_form_nonnegative F V hF x.val

theorem complementAction_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (x : UnitComplement) (M : Q') (hM : (0 : Q')≤M)
    (h : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.abs (F.f t)≤M) :
    RCle (completedInner (complementAction F V x).val (complementAction F V x).val)
      (RCscale (M*M) (completedInner x.val x.val)) :=
  continuousAction_interval_norm_bound F V x.val M hM h

/-- The EXISTING fixed-spacing gap applies to the SAME continuously filtered vector. -/
theorem complementAction_twoStep_form_gap (F : CtsMod) (V : MonotoneOmegaVanishing F) (x : UnitComplement) :
    RCle (completedInner (complementAction F V x).val (twoStepTransfer (complementAction F V x).val))
      (RCscale HalfPow.half (completedInner (complementAction F V x).val (complementAction F V x).val)) :=
  (complement_twoStep_form_gap (complementAction F V x)).2

end YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.center_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.center_polynomialVector
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.continuousAction_center
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.continuousAction_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction_product
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicAllVectorCenteredCalculus.complementAction_twoStep_form_gap
