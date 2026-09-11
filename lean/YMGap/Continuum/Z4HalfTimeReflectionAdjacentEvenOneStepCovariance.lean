/-
# Derived one-step covariance from the adjacent-even centered swap

The two arbitrary strict-cylinder presentations have already been recoded on
one ordered append chart and identified with centered pair-limit assemblies.
This leaf supplies the remaining finite constructive algebra: finite Fubini,
termwise congruence, coefficient commutativity, and the proved entrywise swap.
It then transports the assembly symmetry back to the original one-sided
reflection cross.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCenteredAssembly

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CRealContinuumAlg
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem creal_equiv_refl_local (value : CReal) :
    CReal.Equiv value value := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have hnonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨Q'.add_le_self_of_nonneg _ _ hnonnegative,
    Q'.add_le_self_of_nonneg _ _ hnonnegative⟩

private theorem listCRealSum_congr_on_local
    {State : Type} {left right : State → CReal} :
    ∀ states : List State,
      (∀ state, state ∈ states → CReal.Equiv (left state) (right state)) →
      CReal.Equiv (listCRealSum left states) (listCRealSum right states)
  | [], _ => creal_equiv_refl_local CReal.czero
  | head :: tail, h => by
      have hhead : CReal.Equiv (left head) (right head) :=
        h head List.mem_cons_self
      have htail : CReal.Equiv
          (listCRealSum left tail) (listCRealSum right tail) :=
        listCRealSum_congr_on_local tail
          (fun state hstate => h state (List.mem_cons_of_mem head hstate))
      exact CReal.Equiv.trans
        (CReal.add_congr_left hhead)
        (CReal.add_congr_right htail)

/-- Finite Fubini for constructive-real list sums, proved at every rational
approximation stage from finite rational Fubini. -/
private theorem listCRealSum_swap_local
    {Left Right : Type} (value : Left → Right → CReal)
    (leftStates : List Left) (rightStates : List Right) :
    CReal.Equiv
      (listCRealSum
        (fun right => listCRealSum
          (fun left => value left right) leftStates)
        rightStates)
      (listCRealSum
        (fun left => listCRealSum
          (fun right => value left right) rightStates)
        leftStates) := by
  apply TrigAdd.equiv_of_approx_eqv
  intro stage
  simpa only [listCRealSum_approx] using
    (listQSum_swap
      (fun left right => (value left right).approx stage)
      leftStates rightStates)

/-! ## 1. Exact symmetry of the common centered assembly -/

/-- Swapping the coefficient tables does not change the common one-step
centered assembly.  Finite Fubini reverses the summation order; rational
coefficient commutativity and the derived pair-limit swap identify every
resulting entry. -/
theorem adjacentEvenOneStepCenteredBilinear_swap
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    CReal.Equiv
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle hroots
        leftCoefficient rightCoefficient)
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle hroots
        rightCoefficient leftCoefficient) := by
  let states := strictJointFingerprintSpace roots.length
  let swappedReverse : CReal :=
    listCRealSum
      (fun left => listCRealSum
        (fun right => CReal.mul
          (CReal.ofQ'
            (rightCoefficient right * leftCoefficient left))
          (couplingParametricAdjacentEvenOneStepCenteredPairLimit
            coupling hcoupling hle hroots right left))
        states)
      states
  have hfubini : CReal.Equiv
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle hroots
        rightCoefficient leftCoefficient)
      swappedReverse := by
    unfold adjacentEvenOneStepCenteredBilinear
    dsimp only [swappedReverse, states]
    simpa only using
      (listCRealSum_swap_local
        (fun right left => CReal.mul
          (CReal.ofQ'
            (rightCoefficient left * leftCoefficient right))
          (couplingParametricAdjacentEvenOneStepCenteredPairLimit
            coupling hcoupling hle hroots left right))
        (strictJointFingerprintSpace roots.length)
        (strictJointFingerprintSpace roots.length))
  have htermwise : CReal.Equiv swappedReverse
      (adjacentEvenOneStepCenteredBilinear
        coupling hcoupling hle hroots
        leftCoefficient rightCoefficient) := by
    unfold adjacentEvenOneStepCenteredBilinear
    dsimp only [swappedReverse, states]
    apply listCRealSum_congr_on_local
    intro left hleft
    apply listCRealSum_congr_on_local
    intro right hright
    have hscalar : CReal.Equiv
        (CReal.ofQ' (rightCoefficient right * leftCoefficient left))
        (CReal.ofQ' (leftCoefficient left * rightCoefficient right)) :=
      TrigAdd.equiv_ofQ'_of_eqv
        (Q'.mul_comm_eqv
          (rightCoefficient right) (leftCoefficient left))
    have hentry : CReal.Equiv
        (couplingParametricAdjacentEvenOneStepCenteredPairLimit
          coupling hcoupling hle hroots right left)
        (couplingParametricAdjacentEvenOneStepCenteredPairLimit
          coupling hcoupling hle hroots left right) :=
      couplingParametricAdjacentEvenOneStepCenteredPairLimit_swap
        hcoupling hle hroots right left
    exact CReal.Equiv.trans
      (cmul_congr_left hscalar)
      (cmul_congr_right hentry)
  exact CReal.Equiv.symm (CReal.Equiv.trans hfubini htermwise)

/-! ## 2. Terminal one-step covariance -/

/-- The one-sided strict-cylinder reflection cross is symmetric at shift one.
This is the odd-time covariance statement left open by the polarized
even-time identity. -/
theorem strictJointOneSidedTimeCovariance_one_derived
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointOneSidedTimeCovariance hcoupling hle 1 left right := by
  unfold StrictJointOneSidedTimeCovariance
  exact CReal.Equiv.trans
    (strictJointOneSidedTimeCross_one_equiv_appendForward
      hcoupling hle left right)
    (CReal.Equiv.trans
      (adjacentEvenOneStepCenteredBilinear_swap
        hcoupling hle
        (adjacentEvenOneStepAppendRoots_canonical left right)
        (adjacentEvenOneStepAppendLeftCoefficient left right)
        (adjacentEvenOneStepAppendRightCoefficient left right))
      (CReal.Equiv.symm
        (strictJointOneSidedTimeCross_one_equiv_appendReverse
          hcoupling hle left right)))

#print axioms adjacentEvenOneStepCenteredBilinear_swap
#print axioms strictJointOneSidedTimeCovariance_one_derived

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCovariance
