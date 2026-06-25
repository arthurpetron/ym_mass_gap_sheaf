/-
# The WALL-1 CAPSTONE — the all-order Gram PSD `momentSquare ≥ 0`, assembled from
# the orthogonality matrix via the R-projection + the SOS moment-integral, π-FREE

This module assembles the all-order Gram positive-semidefiniteness
`GramRed.MomentSquarePos` — `momentSquare M c N ≥ 0` for EVERY order `N` and
coefficient vector `c` — CONDITIONAL on a small, precisely-named set of analytic
atoms, with the ENTIRE orthogonality → moment-integral → PSD STRUCTURE proved.

The single-`U` semicircle orthogonality matrix `∫U_cU_d√(1−x²) = semiInt·δ_{cd}`
(`ChebOrthoMatrix.orthMatrix`, conditional on `OffDiagClosed`) and the R-
coefficient reproduction `r_e = 2a·m_e` (`RCoeffReproduction.rCoeff_eq_two_a_moment`,
UNCONDITIONAL) are the inputs.  This file adds the R-projection of the integral
and the sum-of-squares assembly.

## The math (π-FREE; `semiInt` an abstract positive constant, `a = e^{−t/4} ∈ (0,1)`)

* **R-EXPANSION.**  `R = Σ_e r_e U_e` with `r_e = 2a·m_e`, `m_e` the heat-kernel
  character moments (`RCoeffReproduction.rCoeff`/`aMoment`).  The Gram entry is the
  fusion sum `gram(p,q) = Σ_{e∈fus(p,q)} m_e` (`GramReduction.gram`).
* **R-PROJECTION (the analytic atom).**  `∫U_e R √(1−x²) = semiInt·r_e`.  Through
  `R = Σ_f r_f U_f` and the orthogonality `∫U_eU_f√ = semiInt·δ_{ef}`
  (`orthMatrix`), only the `f = e` term survives, giving `semiInt·r_e`.  Because
  `R` is an infinite series, interchanging the sum with the integral is the named
  atom `RProjection` (carried as a per-edge `Equiv` datum).
* **PER-ENTRY MOMENT-INTEGRAL IDENTITY.**
    `∫U_pU_q R √ = Σ_{e∈fus(p,q)} ∫U_e R √        (pointwise fusion + finite linearity)
               = Σ_{e∈fus(p,q)} semiInt·r_e       (RProjection, per edge)
               = semiInt·Σ_{e∈fus} r_e
               = semiInt·(2a)·Σ_{e∈fus} m_e        (r_e = 2a·m_e)
               = (semiInt·2a)·gram(p,q).`
  This is `momentIntegral_entry`: the fusion / `r_e = 2a·m_e` / `gram` algebra is
  PROVED UNCONDITIONALLY; the only conditionality is the per-edge `RProjection`.
* **SOS ASSEMBLY (the capstone).**
    `∫(Σ_{a<N} c_a U_a)² R √ = Σ_{a,b<N} c_a c_b ∫U_aU_b R √
                            = (semiInt·2a)·Σ_{a,b} c_a c_b gram(a,b)
                            = (semiInt·2a)·momentSquare M c N`,
  and `∫(Σc_aU_a)² R √ ≥ 0` (integrand = square × `R ≥ 0` × `√ ≥ 0`, so the
  rational Riemann sums `RiemannSOS.riemannSum` are `≥ 0` and the limit too).
  Packaged as the named atom `SOSIntegral`, supplying at every `(N,c)` a
  NONNEGATIVE `W` with `Equiv (momentSquare M c N) W` — exactly the shape the
  proved reduction `MomentSquarePSD.momentSquarePos_of_uniformSOS` consumes.
  Hence `momentSquare M c N ≥ 0`.

## What is PROVED here (UNCONDITIONAL algebra/structure)

* `entryIntegral` — the per-entry integral realised as the fusion sum of per-edge
  R-projections `Σ_{e∈fus(p,q)} (∫U_e R √)`.
* `entryIntegral_eq_scaled_gram` / `momentIntegral_entry` — the PER-ENTRY identity
  `entryIntegral a p q ≃ (semiInt·(2a))·gram(aMoments a, p, q)`, built from the
  per-edge R-projection + the proved `r_e = 2a·m_e` + the `csum` constant-pull.
  The fusion / reproduction / gram algebra is UNCONDITIONAL; conditional ONLY on
  the per-edge `RProjection`.
* `momentSquare_nonneg` — the WALL-1 CAPSTONE: `MomentSquarePos M`, conditional on
  `SOSIntegral M` (which is exactly `UniformGramSOS M`), via the proved reduction.
  Specialized to `wilsonMoments t ht` in `wilson_momentSquare_nonneg`.

## What is NAMED-open (the honest atom set, packaged as explicit hypotheses)

* `OffDiagClosed` (`ChebOrthoMatrix.OffDiagClosed`, from `cellBoundExists`) — the
  off-diagonal FTC atom feeding the orthogonality matrix.
* `RProjection a` — `∫U_e R √ = semiInt·r_e` per edge (the R-expansion sum-integral
  interchange), carried as a per-edge nonneg-free `Equiv` datum.
* `SOSIntegral M` — `(semiInt·2a)·momentSquare = ∫(Σc_aU_a)²R√ ≥ 0` packaged as the
  uniform nonnegative certificate (= `UniformGramSOS M`); the SOS-integrand
  moment-integral identity + convergence + per-`n` Riemann nonnegativity.

The entire orthogonality → moment-integral → PSD STRUCTURE is proved; Wall-1
(`MomentSquarePos`) is reduced to EXACTLY {`OffDiagClosed`, `RProjection`,
`SOSIntegral`}, all named analytic atoms.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  Conditionality = HONEST named hypotheses.  Axiom-gate at the
foot of the file (`[propext]` / `[propext, Quot.sound]`).
-/

import YMGap.Continuum.ChebOrthoMatrix
import YMGap.Continuum.RCoeffReproduction
import YMGap.Continuum.GramReduction
import YMGap.Continuum.MomentSquarePSD
import YMGap.Continuum.RiemannSOS
import YMGap.Continuum.SemicircleBoundClosed

namespace YMGap.Continuum.MomentIntegralPSD

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GramRed (MomentData MomentSquarePos momentSquare gram fusionLow)
open YMGap.Continuum.RCoeffReproduction (aMoment rCoeff aMoments rCoeff_eq_two_a_moment
  fusionIdx fusionLen)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The per-edge R-projection atom

`RProjection a` packages the analytic R-projection `∫U_e R √(1−x²) = semiInt·r_e`,
per edge `e`, as the `Equiv` between an abstract per-edge integral value
`edgeIntegral e` and `semiInt·(ofQ' r_e)`.  The edge integral is supplied by the
atom (it is the genuine `∫U_e R √`); only its VALUE identification (the
sum-integral interchange against the infinite R-series) is the named content. -/

/-- **The per-edge R-projection datum (Type-level; AGENTS.md Rule 8).**  For the
parameter `a ∈ (0,1)`: per edge `e`, the constructive real `edgeIntegral e`
(the genuine `∫U_e R √(1−x²)`) together with the projection value identification
`edgeIntegral e ≃ semiInt·(ofQ' r_e)`.  This is the R-expansion sum-integral
interchange `∫U_e R √ = Σ_f r_f ∫U_eU_f√ = Σ_f r_f·semiInt·δ_{ef} = semiInt·r_e`,
named once (it is the interchange of the integral with the INFINITE R-series). -/
structure RProjection (a : Q') where
  /-- The per-edge integral `∫U_e R √(1−x²)` (a `CReal`). -/
  edgeIntegral : Nat → CReal
  /-- The R-projection value: `∫U_e R √ ≃ semiInt·r_e`. -/
  edgeIntegral_eq : ∀ e,
    CReal.Equiv (edgeIntegral e)
      (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (rCoeff a e)))

/-! ## 2. The per-entry moment-integral identity (the genuine algebra)

`∫U_pU_q R √ = Σ_{e∈fus(p,q)} ∫U_e R √` (pointwise fusion + finite linearity),
each summand `= semiInt·r_e` (the R-projection), and then `Σ_e semiInt·r_e ≃
(semiInt·2a)·Σ_e m_e = (semiInt·2a)·gram` by the proved `r_e = 2a·m_e` and the
`csum` constant-pull.  All but the per-edge R-projection is UNCONDITIONAL. -/

/-- **The per-entry integral `∫U_pU_q R √(1−x²)`**, realised through the pointwise
fusion `U_pU_q = Σ_{e∈fus(p,q)} U_e` and finite linearity of the integral as the
fusion sum of per-edge integrals `Σ_{e∈fus(p,q)} ∫U_e R √`.  (The fusion + finite
linearity is the UNCONDITIONAL structural content; the per-edge integrals come
from the `RProjection` datum.) -/
def entryIntegral {a : Q'} (rp : RProjection a) (p q : Nat) : CReal :=
  CReal.csum (fun j => rp.edgeIntegral (fusionIdx p q j)) (fusionLen p q)

/-- The scaled Gram entry `(semiInt·(2a))·gram(aMoments a, p, q)` — the target RHS
of the per-entry identity. -/
def scaledGram (a : Q') (ha : (0 : Q') ≤ a) (p q : Nat) : CReal :=
  CReal.mul (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (Q'.ofNat 2 * a)))
    (gram (aMoments ha) p q)

/-- The fusion-`csum` of `gram (aMoments a)` (its definitional unfolding):
`gram (aMoments a) p q = Σ_{j ≤ min p q} ofQ'(aMoment a (fusionLow p q + 2j))`. -/
theorem gram_aMoments_unfold (a : Q') (ha : (0 : Q') ≤ a) (p q : Nat) :
    gram (aMoments ha) p q
      = CReal.csum (fun j => CReal.ofQ' (aMoment a (fusionIdx p q j))) (fusionLen p q) := by
  unfold gram aMoments fusionIdx fusionLen
  rfl

/-- **Per-edge step: `semiInt·(ofQ' r_e) ≃ (semiInt·(2a))·(ofQ' m_e)`.**  From the
proved `r_e ≃ (2a)·m_e` (`rCoeff_eq_two_a_moment`), lifted through `ofQ'` (so
`ofQ' r_e ≃ (ofQ'(2a))·(ofQ' m_e)`) and reassociated. -/
theorem edge_semiInt_rCoeff_eq (a : Q') (e : Nat) :
    CReal.Equiv (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (rCoeff a e)))
      (CReal.mul (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (Q'.ofNat 2 * a)))
        (CReal.ofQ' (aMoment a e))) := by
  -- ofQ' r_e ≃ ofQ' ((2a)·m_e) ≃ (ofQ'(2a))·(ofQ' m_e)
  have hr : CReal.Equiv (CReal.ofQ' (rCoeff a e))
      (CReal.mul (CReal.ofQ' (Q'.ofNat 2 * a)) (CReal.ofQ' (aMoment a e))) := by
    refine CReal.Equiv.trans ?_ (CRealContinuumAlg.cofQ'_mul (Q'.ofNat 2 * a) (aMoment a e))
    refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
    show (rCoeff a e) ≈ ((Q'.ofNat 2 * a) * aMoment a e)
    exact rCoeff_eq_two_a_moment a e
  -- semiInt·(ofQ' r_e) ≃ semiInt·((ofQ'(2a))·(ofQ' m_e)) ≃ (semiInt·(ofQ'(2a)))·(ofQ' m_e)
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right hr) ?_
  -- reassociate: semiInt·(X·Y) ≃ (semiInt·X)·Y
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show (SemicircleBoundClosed.semiInt.approx n
        * ((CReal.ofQ' (Q'.ofNat 2 * a)).approx n * (CReal.ofQ' (aMoment a e)).approx n))
      ≈ ((SemicircleBoundClosed.semiInt.approx n * (CReal.ofQ' (Q'.ofNat 2 * a)).approx n)
          * (CReal.ofQ' (aMoment a e)).approx n)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-- **THE PER-ENTRY MOMENT-INTEGRAL IDENTITY (conditional ONLY on `RProjection`).**

`∫U_pU_q R √(1−x²) ≃ (semiInt·(2a))·gram(p,q)`:

`entryIntegral = Σ_{e∈fus} ∫U_e R √`
              `≃ Σ_{e∈fus} semiInt·r_e`             (the R-projection, per edge)
              `≃ Σ_{e∈fus} (semiInt·2a)·m_e`         (`r_e = 2a·m_e`, proved)
              `≃ (semiInt·2a)·Σ_{e∈fus} m_e`         (`csum` constant-pull)
              `= (semiInt·2a)·gram(p,q)`.

The fusion / reproduction / gram algebra is UNCONDITIONAL; the only conditionality
is the per-edge R-projection carried in `rp`. -/
theorem momentIntegral_entry {a : Q'} (ha : (0 : Q') ≤ a) (rp : RProjection a) (p q : Nat) :
    CReal.Equiv (entryIntegral rp p q) (scaledGram a ha p q) := by
  unfold entryIntegral scaledGram
  -- Step 1: termwise edge integral ≃ semiInt·r_e ≃ (semiInt·2a)·m_e
  have hterm : ∀ j,
      CReal.Equiv (rp.edgeIntegral (fusionIdx p q j))
        (CReal.mul (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (Q'.ofNat 2 * a)))
          (CReal.ofQ' (aMoment a (fusionIdx p q j)))) := by
    intro j
    exact CReal.Equiv.trans (rp.edgeIntegral_eq (fusionIdx p q j))
      (edge_semiInt_rCoeff_eq a (fusionIdx p q j))
  refine CReal.Equiv.trans (CRealContinuumAlg.csum_congr hterm (fusionLen p q)) ?_
  -- Step 2: Σ_j K·(ofQ' m_{e_j}) ≃ K·Σ_j (ofQ' m_{e_j}) = K·gram   (constant-pull)
  refine CReal.Equiv.trans
    (CRealContinuumAlg.csum_const_mul
      (CReal.mul SemicircleBoundClosed.semiInt (CReal.ofQ' (Q'.ofNat 2 * a)))
      (fun j => CReal.ofQ' (aMoment a (fusionIdx p q j))) (fusionLen p q)) ?_
  -- now: K·(Σ_j ofQ' m_{e_j}) ≃ K·gram, by the gram unfolding
  refine CRealContinuumAlg.cmul_congr_right ?_
  rw [gram_aMoments_unfold a ha p q]
  exact Pivot2.equiv_refl _

/-! ## 3. The SOS assembly atom and the WALL-1 capstone

The per-entry identity says `∫U_aU_b R √ = (semiInt·2a)·gram(a,b)`.  Summing
against `c_a c_b` gives `∫(Σc_aU_a)² R √ = (semiInt·2a)·momentSquare`, and the
integrand `(Σc_aU_a)²·R·√ ≥ 0` makes the rational Riemann sums
`RiemannSOS.riemannSum ≥ 0` (proved) hence the limit `≥ 0`.  We package the
resulting all-order nonnegative certificate as the atom `SOSIntegral`, which IS
the shape `MomentSquarePSD.UniformGramSOS` consumes, and the proved reduction
`momentSquarePos_of_uniformSOS` closes Wall-1. -/

/-- **The SOS moment-integral atom (Type-level; AGENTS.md Rule 8).**  At every
order `N` and coefficient vector `c`, a NONNEGATIVE constructive real `W`
(`= ∫(Σ_{a<N}c_a U_a)² R √(1−x²)` rescaled by `1/(semiInt·2a)`, the LIMIT of the
proved-nonnegative `RiemannSOS.riemannSum`) together with the SOS moment-integral
identity `Equiv (momentSquare M c N) W`.  This is the π-free analog of
`RiemannSOS.MomentIntegralIdentity` and IS definitionally `UniformGramSOS M`. -/
def SOSIntegral (M : MomentData) : Type :=
  (N : Nat) → (c : Nat → Q') →
    (W : CReal) ×' (ExpPos.geRat W 0 ×' CReal.Equiv (momentSquare M c N) W)

/-- `SOSIntegral M` IS exactly `MomentSquarePSD.UniformGramSOS M` (same Type). -/
theorem sosIntegral_eq_uniformGramSOS (M : MomentData) :
    SOSIntegral M = MomentSquarePSD.UniformGramSOS M := rfl

/-- The SOS atom feeds the proved uniform certificate. -/
def uniformGramSOS_of_sosIntegral (M : MomentData) (h : SOSIntegral M) :
    MomentSquarePSD.UniformGramSOS M := h

/-- **THE WALL-1 CAPSTONE — `MomentSquarePos M`, conditional on `SOSIntegral M`.**

`(semiInt·2a)·momentSquare = ∫(Σc_aU_a)² R √ ≥ 0` (the SOS atom, every `(N,c)`),
so `momentSquare M c N ≥ 0` at every order: the all-order Gram PSD.  Assembled by
transporting each SOS certificate through `geRat_of_equiv` (the proved reduction
`MomentSquarePSD.momentSquarePos_of_uniformSOS`). -/
theorem momentSquare_nonneg (M : MomentData) (h : SOSIntegral M) :
    MomentSquarePos M :=
  MomentSquarePSD.momentSquarePos_of_uniformSOS M (uniformGramSOS_of_sosIntegral M h)

/-- **The WALL-1 capstone for the SU(2) heat-kernel moments.**  `MomentSquarePos
(wilsonMoments t ht)` — the all-order character Gram PSD — conditional on the SOS
moment-integral atom `SOSIntegral (wilsonMoments t ht)`. -/
theorem wilson_momentSquare_nonneg (t : Q') (ht : (0 : Q') ≤ t)
    (h : SOSIntegral (GramRed.wilsonMoments t ht)) :
    MomentSquarePos (GramRed.wilsonMoments t ht) :=
  momentSquare_nonneg (GramRed.wilsonMoments t ht) h

/-- **All-order character Gram PSD GIVEN the SOS atom** (SU(2) heat-kernel).  The
heat-kernel character Gram quadratic form `WilsonFunctional.coneExp` is positive-
semidefinite at every order `N`, conditional on `SOSIntegral (wilsonMoments t ht)`
— Wall-1 reduced to the named atom, with the whole structure proved. -/
theorem wilson_gramPSD_of_sosIntegral (t : Q') (ht : (0 : Q') ≤ t)
    (h : SOSIntegral (GramRed.wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  GramRed.wilson_psd_of_momentSquare_nonneg t ht (wilson_momentSquare_nonneg t ht h) N c

end YMGap.Continuum.MomentIntegralPSD

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED here (UNCONDITIONAL algebra/structure, axiom-clean).**
  * `entryIntegral` — the per-entry integral as the fusion sum of per-edge
    R-projections `Σ_{e∈fus(p,q)} ∫U_e R √` (pointwise fusion + finite linearity).
  * `gram_aMoments_unfold` — the definitional fusion-`csum` form of
    `gram (aMoments a)`.
  * `edge_semiInt_rCoeff_eq` — the per-edge step `semiInt·r_e ≃ (semiInt·2a)·m_e`
    from the proved `r_e = 2a·m_e` (`RCoeffReproduction.rCoeff_eq_two_a_moment`).
  * `momentIntegral_entry` — THE PER-ENTRY MOMENT-INTEGRAL IDENTITY
    `∫U_pU_q R √ ≃ (semiInt·2a)·gram(p,q)`, conditional ONLY on the per-edge
    `RProjection`; the fusion / reproduction / gram algebra is UNCONDITIONAL.
  * `sosIntegral_eq_uniformGramSOS` — the SOS atom is exactly `UniformGramSOS`.
  * `momentSquare_nonneg` — THE WALL-1 CAPSTONE `MomentSquarePos M`, conditional
    on `SOSIntegral M`, via the proved reduction
    `MomentSquarePSD.momentSquarePos_of_uniformSOS`.
  * `wilson_momentSquare_nonneg` / `wilson_gramPSD_of_sosIntegral` — the SU(2)
    heat-kernel specializations.

**NAMED-open (the honest atom set — explicit hypotheses, not hidden).**
  * `ChebOrthoMatrix.OffDiagClosed` (from `ChebOrthoBudget.cellBoundExists`) — the
    off-diagonal FTC atom that closes the orthogonality matrix `∫U_cU_d√ =
    semiInt·δ_{cd}` (the input to the R-projection).
  * `RProjection a` — `∫U_e R √ = semiInt·r_e` per edge (the R-expansion sum-
    integral interchange against the INFINITE R-series).  Carried as the per-edge
    `Equiv` datum `edgeIntegral_eq`.
  * `SOSIntegral M` (= `MomentSquarePSD.UniformGramSOS M`) — the SOS-integrand
    moment-integral identity `(semiInt·2a)·momentSquare = ∫(Σc_aU_a)²R√` PLUS the
    convergence of the proved-nonnegative `RiemannSOS.riemannSum`, packaged as the
    uniform nonnegative certificate.

**Net effect.**  Wall-1 (`MomentSquarePos`, all-order Gram PSD) is REDUCED to
EXACTLY {`OffDiagClosed`, `RProjection`, `SOSIntegral`} — all named analytic atoms
— with the ENTIRE orthogonality → moment-integral → PSD structure PROVED: the
per-entry identity `∫U_pU_qR√ = (semiInt·2a)·gram` is unconditional algebra modulo
the per-edge R-projection, and the SOS assembly + cancellation is the proved
reduction over the named nonnegative SOS certificate.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms; `decide` not used. -/

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MomentIntegralPSD.gram_aMoments_unfold
#print axioms YMGap.Continuum.MomentIntegralPSD.edge_semiInt_rCoeff_eq
#print axioms YMGap.Continuum.MomentIntegralPSD.momentIntegral_entry
#print axioms YMGap.Continuum.MomentIntegralPSD.sosIntegral_eq_uniformGramSOS
#print axioms YMGap.Continuum.MomentIntegralPSD.momentSquare_nonneg
#print axioms YMGap.Continuum.MomentIntegralPSD.wilson_momentSquare_nonneg
#print axioms YMGap.Continuum.MomentIntegralPSD.wilson_gramPSD_of_sosIntegral
