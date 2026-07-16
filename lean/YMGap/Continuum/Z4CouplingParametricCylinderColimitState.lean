/-
# The coupling-parametric finite-cylinder colimit state

The simultaneous cutoff/volume values are evaluated on quotient-free finite
cylinder presentations and shown invariant under explicit common-refinement
equivalence.  Normalization, positivity, complement, and disjoint finite
additivity are bundled into one constructive state over the presentation
colimit for every exact rational coupling below the anchor.

This is a finitely additive state on local Boolean cylinder events.  It does
not by itself supply countable additivity, a configuration-space measure, or
reflection positivity and OS reconstruction.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
import YMGap.Continuum.Z4FiniteCylinderPresentationColimit

namespace YMGap.Continuum.Z4CouplingParametricCylinderColimitState

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4SpinSummedCutoffTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A quotient-free state interface -/

/-- A constructive probability state on the finite-cylinder presentation
colimit.  Boolean laws are chartwise; `respects` makes their values independent
of the chosen representative. -/
structure FiniteCylinderColimitState where
  evaluate : FiniteCylinderPresentation → CReal
  respects : ∀ left right,
    CylinderPresentationEquivalent left right →
      CReal.Equiv (evaluate left) (evaluate right)
  nonnegative : ∀ presentation,
    CReal.ofQ' 0 ≤ evaluate presentation
  le_one : ∀ presentation,
    evaluate presentation ≤ CReal.ofQ' 1
  normalized : ∀ (chart : FiniteCylinderChart),
    CReal.Equiv
      (evaluate (chart.present (fun _ => true)))
      (CReal.ofQ' 1)
  empty : ∀ (chart : FiniteCylinderChart),
    CReal.Equiv
      (evaluate (chart.present (fun _ => false)))
      (CReal.ofQ' 0)
  complement : ∀ (presentation : FiniteCylinderPresentation),
    CReal.Equiv
      (CReal.add
        (evaluate presentation)
        (evaluate
          (presentation.chart.present
            (complementCylinderPredicate presentation.predicate))))
      (CReal.ofQ' 1)
  disjoint_additive : ∀ (chart : FiniteCylinderChart)
      (first second : List Bool → Bool),
    CylinderPredicatesDisjoint first second →
      CReal.Equiv
        (evaluate
          (chart.present (cylinderPredicateUnion first second)))
        (CReal.add
          (evaluate (chart.present first))
          (evaluate (chart.present second)))

/-! ## 2. Evaluation of a finite presentation -/

def couplingParametricCylinderPresentationValue
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : FiniteCylinderPresentation) : CReal :=
  couplingParametricSpinSummedJointCylinderLimitFunctional
    coupling hcoupling hle presentation.chart.rootsCanonical
      presentation.predicate

private theorem equiv_ofQ'_of_eqv_local {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_local {A B : CReal}
    (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_local (h stage))

/-- The value of a larger presentation equals the value of the event it
refines.  Exact equality at matched outer boxes handles the presentation
change; the previously derived base-transport modulus handles the base box. -/
theorem couplingParametricCylinderPresentationValue_refines
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {source target : FiniteCylinderPresentation}
    (hrefines : CylinderPresentationRefines source target) :
    CReal.Equiv
      (couplingParametricCylinderPresentationValue
        coupling hcoupling hle target)
      (couplingParametricCylinderPresentationValue
        coupling hcoupling hle source) := by
  let transported :=
    source.transport target.chart.base hrefines.base_le
  have hexact :
      CReal.Equiv
        (couplingParametricCylinderPresentationValue
          coupling hcoupling hle target)
        (couplingParametricCylinderPresentationValue
          coupling hcoupling hle transported) := by
    apply creal_equiv_of_approx_eqv_local
    intro stage
    change couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling
        (spinSummedJointCutoff stage (target.chart.base + stage))
        (target.chart.base + stage)
        (targetCylinderEvent target.chart.base
          (target.chart.base + stage) target.chart.roots
          target.predicate) ≈
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling
        (spinSummedJointCutoff stage (target.chart.base + stage))
        (target.chart.base + stage)
        (targetCylinderEvent target.chart.base
          (target.chart.base + stage)
          (transportedCylinderRoots source.chart.base
            target.chart.base source.chart.roots)
          source.predicate)
    rw [hrefines.event_eq (target.chart.base + stage) (by omega)]
    rw [targetCylinderEvent_trans hrefines.base_le (by omega)
      source.chart.rootsCanonical source.predicate]
    exact Q'.eqv_refl _
  have hbase :=
    couplingParametricSpinSummedJointCylinderLimitFunctional_base_transport
      hcoupling hle hrefines.base_le source.chart.rootsCanonical
        source.predicate
  exact CReal.Equiv.trans hexact hbase

/-- Evaluation is well-defined on common-refinement equivalence classes. -/
theorem couplingParametricCylinderPresentationValue_respects
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {left right : FiniteCylinderPresentation}
    (hequivalent : CylinderPresentationEquivalent left right) :
    CReal.Equiv
      (couplingParametricCylinderPresentationValue
        coupling hcoupling hle left)
      (couplingParametricCylinderPresentationValue
        coupling hcoupling hle right) := by
  rcases hequivalent with ⟨common, hleft, hright⟩
  have hleftValue :=
    couplingParametricCylinderPresentationValue_refines
      hcoupling hle hleft
  have hrightValue :=
    couplingParametricCylinderPresentationValue_refines
      hcoupling hle hright
  exact CReal.Equiv.trans (CReal.Equiv.symm hleftValue) hrightValue

/-! ## 3. The bundled colimit state -/

def couplingParametricFiniteCylinderColimitState
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) :
    FiniteCylinderColimitState where
  evaluate := couplingParametricCylinderPresentationValue
    coupling hcoupling hle
  respects := fun _ _ hequivalent =>
    couplingParametricCylinderPresentationValue_respects
      hcoupling hle hequivalent
  nonnegative := fun presentation =>
    couplingParametricSpinSummedJointCylinderLimitFunctional_nonnegative
      hcoupling hle presentation.chart.rootsCanonical
        presentation.predicate
  le_one := fun presentation =>
    couplingParametricSpinSummedJointCylinderLimitFunctional_le_one
      hcoupling hle presentation.chart.rootsCanonical
        presentation.predicate
  normalized := fun chart =>
    couplingParametricSpinSummedJointCylinderLimitFunctional_normalized
      hcoupling hle chart.rootsCanonical
  empty := fun chart =>
    couplingParametricSpinSummedJointCylinderLimitFunctional_empty
      hcoupling hle chart.rootsCanonical
  complement := fun presentation =>
    couplingParametricSpinSummedJointCylinderLimitFunctional_complement
      hcoupling hle presentation.chart.rootsCanonical
        presentation.predicate
  disjoint_additive := fun chart first second hdisjoint =>
    couplingParametricSpinSummedJointCylinderLimitFunctional_disjoint_additive
      hcoupling hle chart.rootsCanonical first second hdisjoint

theorem couplingParametricFiniteCylinderColimitState_transport
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : FiniteCylinderPresentation)
    (outerBase : Nat) (hbase : presentation.chart.base ≤ outerBase) :
    CReal.Equiv
      ((couplingParametricFiniteCylinderColimitState
        coupling hcoupling hle).evaluate
          (presentation.transport outerBase hbase))
      ((couplingParametricFiniteCylinderColimitState
        coupling hcoupling hle).evaluate presentation) :=
  (couplingParametricFiniteCylinderColimitState
    coupling hcoupling hle).respects _ _
      (presentation.equivalent_transport outerBase hbase)

theorem couplingParametricFiniteCylinderColimitState_appendIgnored
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (presentation : FiniteCylinderPresentation)
    (extra : List (List Nat))
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers presentation.chart.base) :
    CReal.Equiv
      ((couplingParametricFiniteCylinderColimitState
        coupling hcoupling hle).evaluate
          (presentation.appendIgnored extra hextra))
      ((couplingParametricFiniteCylinderColimitState
        coupling hcoupling hle).evaluate presentation) :=
  (couplingParametricFiniteCylinderColimitState
    coupling hcoupling hle).respects _ _
      (presentation.equivalent_appendIgnored extra hextra)

#print axioms couplingParametricCylinderPresentationValue_refines
#print axioms couplingParametricCylinderPresentationValue_respects
#print axioms couplingParametricFiniteCylinderColimitState
#print axioms couplingParametricFiniteCylinderColimitState_transport
#print axioms couplingParametricFiniteCylinderColimitState_appendIgnored

end YMGap.Continuum.Z4CouplingParametricCylinderColimitState
