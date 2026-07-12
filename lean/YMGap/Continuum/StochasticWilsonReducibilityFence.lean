/-
# Stochastic-quantization dead-route fence: the off-diagonal Wilson chain is reducible

`CharChainWilson.chainW β` is a finite reversible Markov generator on the three
character channels `0,1,2`.  Its only transition is `0 ↔ 2`; channel `1` is
isolated.  This file records the exact consequence relevant to any stochastic-
quantization gap route: for every coupling `β`, the generator has a nonconstant,
mean-zero, positive-norm zero eigenmode.

Take `componentMode = (1,-2,1)`.  It is constant on the communicating class
`{0,2}` and arbitrary on the isolated class `{1}`, hence `L componentMode = 0`.
Against `chainW`'s uniform weight `π=1/2`, its mean is zero and squared norm is
`3 > 0`.  Therefore no positive Poincaré inequality

    κ E[f²] ≤ E[Γ(f)]

can hold for every mean-zero `f`: on this mode the right side is zero while the
left side is strictly positive for every `κ>0`.

This is a finite exact obstruction, not a statement about the physical Yang–Mills
generator.  It fences off the off-diagonal-only surrogate as a route to the
canonical positive continuum margin.  A viable stochastic formulation must add
actual transitions joining all character sectors and prove their physical
identification; it cannot import a free curvature floor from a different chain.

Constructive contract: exact `Q'`, finite sums, kernel `decide` only.  No
`Classical.*`, `Real`, `native_decide`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CharChainWilson

namespace YMGap.Continuum.StochasticWilsonReducibilityFence

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BakryEmery
open YMGap.Continuum.CharChainWilson

/-- A function constant on the communicating class `{0,2}` and different on
the isolated channel `1`: `(f 0,f 1,f 2)=(1,-2,1)`. -/
def componentMode (x : Nat) : Q' := if x = 1 then (-2 : Q') else 1

theorem componentMode_values :
    componentMode 0 = 1 ∧ componentMode 1 = (-2 : Q') ∧ componentMode 2 = 1 := by
  decide

/-- The reducibility witness is nonconstant. -/
theorem componentMode_nonconstant : ¬ (componentMode 0).eqv (componentMode 1) := by
  decide

/-- Channel `1` is an isolated column of the Wilson generator. -/
theorem wilsonW_col_one_zero (β : Q') (x : Nat) :
    wilsonW β x 1 = (0 : Q') := by
  unfold wilsonW
  simp

/-- The off-diagonal Wilson generator annihilates the component mode at every
state, for every coupling. -/
theorem componentMode_Lapp_zero (β : Q') (x : Nat) :
    ((chainW β).Lapp componentMode x).eqv 0 := by
  unfold RevGen.Lapp
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun y => wilsonW β x y * componentMode y)
      (fun y => wilsonW β x y) (fun y => ?_) 3) ?_
  · by_cases hy : y = 1
    · subst hy
      dsimp
      rw [wilsonW_col_one_zero]
      exact Q'.eqv_trans _ _ _ (Q'.zero_mul_eqv _) (Q'.eqv_refl 0)
    · dsimp
      unfold componentMode
      rw [if_neg hy]
      exact Q'.mul_one_eqv _
  · exact (chainW β).rowSumZero x

/-- The component mode is an exact zero eigenfunction of `chainW β`. -/
theorem componentMode_zero_eigen (β : Q') :
    (chainW β).Eigen componentMode 0 := by
  intro x
  refine Q'.eqv_trans _ _ _ (componentMode_Lapp_zero β x) ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv _)) ?_
  decide

/-- The component mode is centered: `Eπ[f]=0`. -/
theorem componentMode_mean_zero (β : Q') :
    ((chainW β).E componentMode).eqv 0 := by
  unfold RevGen.E
  show (((0 : Q') + Q'.mkPos 1 2 (by decide) * componentMode 0
      + Q'.mkPos 1 2 (by decide) * componentMode 1
      + Q'.mkPos 1 2 (by decide) * componentMode 2)).eqv 0
  rw [componentMode_values.1, componentMode_values.2.1, componentMode_values.2.2]
  decide

/-- Its squared norm is exactly `3`, hence strictly positive. -/
theorem componentMode_norm_sq (β : Q') :
    ((chainW β).E (RevGen.pmul componentMode componentMode)).eqv 3 := by
  unfold RevGen.E RevGen.pmul
  show (((0 : Q')
      + Q'.mkPos 1 2 (by decide) * (componentMode 0 * componentMode 0)
      + Q'.mkPos 1 2 (by decide) * (componentMode 1 * componentMode 1)
      + Q'.mkPos 1 2 (by decide) * (componentMode 2 * componentMode 2))).eqv 3
  rw [componentMode_values.1, componentMode_values.2.1, componentMode_values.2.2]
  decide

theorem componentMode_norm_pos (β : Q') :
    (0 : Q') < (chainW β).E (RevGen.pmul componentMode componentMode) := by
  exact Q'.pos_of_lt_of_le (by decide : (0 : Q') < 3)
    (Q'.le_of_eqv (Q'.eqv_symm (componentMode_norm_sq β)))

/-- The zero mode has zero Dirichlet energy, by the exact Dirichlet/eigen
identity. -/
theorem componentMode_dirichlet_zero (β : Q') :
    ((chainW β).E ((chainW β).Gamma1 componentMode)).eqv 0 := by
  refine Q'.eqv_trans _ _ _
    ((chainW β).dirichlet_eigen componentMode 0 (componentMode_zero_eigen β)) ?_
  exact Q'.zero_mul_eqv _

/-- **Positive Poincaré obstruction.**  No strictly positive `κ` can bound the
mean-zero component mode by its Dirichlet energy. -/
theorem no_positive_poincare_on_componentMode (β κ : Q') (hκ : (0 : Q') < κ) :
    ¬ (κ * (chainW β).E (RevGen.pmul componentMode componentMode)
        ≤ (chainW β).E ((chainW β).Gamma1 componentMode)) := by
  intro hP
  have hleft : (0 : Q') < κ * (chainW β).E (RevGen.pmul componentMode componentMode) :=
    BakryEmery.mul_pos hκ (componentMode_norm_pos β)
  have hzero : (chainW β).E ((chainW β).Gamma1 componentMode) ≤ (0 : Q') :=
    Q'.le_of_eqv (componentMode_dirichlet_zero β)
  have hltzero : (0 : Q') < (0 : Q') :=
    Q'.pos_of_lt_of_le hleft (Q'.le_trans' _ _ _ hP hzero)
  exact Int.lt_irrefl _ hltzero

/-- Type-level witness packaging the extra stationary sector: nonconstant,
centered, positive norm, and zero energy. -/
def reducibilityWitness (β : Q') :
    Σ' f : Nat → Q',
      (chainW β).Eigen f 0 ∧
      (¬ (f 0).eqv (f 1)) ∧
      ((chainW β).E f).eqv 0 ∧
      (0 : Q') < (chainW β).E (RevGen.pmul f f) :=
  ⟨componentMode, componentMode_zero_eigen β, componentMode_nonconstant,
    componentMode_mean_zero β, componentMode_norm_pos β⟩

end YMGap.Continuum.StochasticWilsonReducibilityFence

#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.componentMode_Lapp_zero
#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.componentMode_zero_eigen
#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.componentMode_mean_zero
#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.componentMode_norm_sq
#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.componentMode_dirichlet_zero
#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.no_positive_poincare_on_componentMode
#print axioms YMGap.Continuum.StochasticWilsonReducibilityFence.reducibilityWitness
