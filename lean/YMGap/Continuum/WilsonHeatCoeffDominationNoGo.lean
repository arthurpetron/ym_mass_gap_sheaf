/-
# NO-GO: Wilson character coefficients are not dominated by the BF4 heat-kernel weight

**Labels: U(1)-true; rules out coefficient-domination bridges; not gap evidence.**

Candidate (c) for `BF4StrongCouplingClusteringBridge.TorusChiBridge` would compare the
SU(2) Wilson torus with the BF4 heat-kernel carrier through a coefficient bound
`c_s^{(K)} ≤ c_0^{(K)} · coeffW w s`.  Here `c_s^{(K)} = wCoeff (wilsonA β) K s` are the
exact character coefficients of the truncated Wilson weight `T_K`
(`SU2WilsonCharacterPower.wilsonPoly_expand`).  `coeffW w s = (s+1) w^{s(s+2)}` is the BF4
heat-kernel plaquette coefficient (`BondMovingStep.coeffW`, used by `heatKernelPacket`).
The bound is required for every truncation order `K` and every spin `s ≤ K`.

At the actual pilot couplings `β = betaS = 1/(2·10¹²)` and `w = 1/1024`
(`BF4ExactSlabPlaquetteSmallNomeCertificate.nome`):

* `pilot_K2_dominated`: the bound HOLDS for `K = 2` and all `s ≤ 2`.
* `wilson_coeff_counterexample`: it FAILS at `K = s = 3`.  The left side is
  `c_3 = (β/2)³/3! = 1/(3.84·10³⁸)`.  The right side is
  `c_0 · coeffW w 3 = (1 + (β/2)²/2) · 4·2⁻¹⁵⁰ ≈ 2.8·10⁻⁴⁵`.
* `wilson_coeff_counterexample_K4`: it also fails at `K = s = 4`.
* `wilson_not_coeffDominated`: hence `¬ CoeffDominated (wilsonA betaS) nome`.

The cause is factorial versus Gaussian decay in `s`.  Domination therefore fails at every
fixed `w < 1` for large enough `K` (not formalised here; only the pilot instance is proved).
Even when domination holds, it would bound polymer activities, not correlators across two
measures.  No GKS-type monotonicity is available for signed non-abelian activities.

All checks are `decide` on explicit rationals.  No new hypotheses.  The same failure occurs
for U(1) with Bessel coefficients against `w^{n²}`.  NOT a gap, continuum or Clay claim.
-/

import YMGap.Continuum.SU2LinkDecaySharpInst
import YMGap.Continuum.SU2WilsonActivity
import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

namespace YMGap.Continuum.WilsonHeatCoeffDominationNoGo

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2WilsonCharacterPower (wCoeff)
open YMGap.Continuum.SU2WilsonActivity (wilsonA)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.SU2LinkDecaySharpInst (betaS)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)

/-- Coefficient domination of a Taylor weight `a` by the heat-kernel weight at nome `w`,
uniformly in the truncation order `K`: `c_s^{(K)} ≤ c_0^{(K)} · coeffW w s` for all `s ≤ K`. -/
def CoeffDominated (a : Nat → Q') (w : Q') : Prop :=
  ∀ K s : Nat, s ≤ K → wCoeff a K s ≤ wCoeff a K 0 * coeffW w s

/-- At truncation `K = 2` the pilot Wilson weight IS dominated (all `s ≤ 2`). -/
theorem pilot_K2_dominated :
    ∀ s : Nat, s ≤ 2 → wCoeff (wilsonA betaS) 2 s ≤ wCoeff (wilsonA betaS) 2 0 * coeffW nome s
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | n + 3, h => absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 2 < 3) (Nat.le_add_left 3 n)) h)
      (Nat.lt_irrefl 2)

/-- **Counterexample `K = s = 3`.**  `c_3 = 1/(3.84·10³⁸)` exceeds `c_0 · 4·2⁻¹⁵⁰`. -/
theorem wilson_coeff_counterexample :
    ¬ (wCoeff (wilsonA betaS) 3 3 ≤ wCoeff (wilsonA betaS) 3 0 * coeffW nome 3) := by
  decide

/-- The left side of the counterexample, exactly: `c_3^{(3)} = (β/2)³/3!`. -/
theorem counterexample_lhs :
    Q'.eqv (wCoeff (wilsonA betaS) 3 3) ⟨1, 383999999999999999999999999999999999999⟩ := by
  decide

/-- The violation persists at `K = s = 4`. -/
theorem wilson_coeff_counterexample_K4 :
    ¬ (wCoeff (wilsonA betaS) 4 4 ≤ wCoeff (wilsonA betaS) 4 0 * coeffW nome 4) := by
  decide

/-- **NO-GO.**  The pilot Wilson weight is not coefficient-dominated by the pilot BF4
heat-kernel weight uniformly in `K`.  U(1)-true; rules out coefficient-domination bridges;
not gap evidence. -/
theorem wilson_not_coeffDominated : ¬ CoeffDominated (wilsonA betaS) nome :=
  fun h => wilson_coeff_counterexample (h 3 3 (Nat.le_refl 3))

end YMGap.Continuum.WilsonHeatCoeffDominationNoGo
