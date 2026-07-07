/-
Track B / R2 — THE RG-INVARIANT SCALE `Λ = μ·exp(−1/(2β₀g²))` AS A CONCRETE CReal:
the dimensional-transmutation invariant, its EXACT self-similar RG step, and the
honest verdict on whether the constructive non-perturbative RG GENERATES the real Λ
or reduces to the single per-step defect `singleStep` / the interacting-measure
substrate.

# What this module adds (read first)

`CondensateGeometricErosion` built the condensate factor
`exp(−c/(β₀g_k²)) = exp(−c(k+B)/(β₀A)) = condensateCReal k` — the lattice-unit scale
`a_k·Λ`, a genuine irrational CReal in `[0,1]`, geometric with ratio
`ρ = exp(−c/(β₀A)) = exp(−6/11)`.  `DimensionlessMarginTransmutation` built the
CONSERVED dimensionless margin along the ideal irrational self-similar flow
(`dimMargin_conserved_concreteE`).  What was NOT yet made explicit is the object the
task names: the **RG-INVARIANT dimensionful scale** `Λ_k = μ_k·exp(−c/(β₀g_k²))`
(`μ_k = 1/a_k` the RG scale), and the machine-checked statement of *why* it is a flow
invariant — the EXACT self-similar RG step of the essential-singularity factor.

This module supplies:

  * **`condensate_selfSimilar_step`** (PROVED, unconditional) — the essential-singularity
    factor is EXACTLY self-similar under one RG step:
        `condensateCReal (k+1)  ≃  condensateCReal k · ρ`,   `ρ = exp(−6/11)`,
    a FIXED multiplicative ratio per block-spin step.  Proved via the exponential
    addition law `expNeg_add_equiv` (`e^{−a}·e^{−b} ≃ e^{−(a+b)}`) applied to the
    exponent recursion `condExponent (k+1) ≃ condExponent k + condRateExp`.  This IS
    the RG-invariance of `Λ` in mechanism form: the condensate shrinks by `ρ` each
    step, so `Λ = μ·condensate` is conserved iff the RG scale `μ` grows by exactly
    `1/ρ` per step (the matched self-similar spacing law).

  * **`rgScaleLambda` / `rgScaleLambda_conserved`** (CONDITIONAL) — the dimensionful
    RG-invariant `Λ_k = μ_k·condensateCReal k` is CONSERVED (`Λ_k ≃ Λ_{k+1}`) exactly
    when the RG scale obeys the matched self-similar law `ρ·μ_{k+1} ≃ μ_k`.  The
    matched-spacing hypothesis is the DIAL (the ideal `ε ≡ 0` self-similar trajectory);
    it is left as an OPEN binder — the module inhabits no dimensionful `Λ` unconditionally.

  * **`rgInvariant_mechanism_nonvacuous`** (re-export, unconditional) — the RG-invariant
    mechanism is GENUINE, not vacuous: the dimensionless margin
    `(1 − sep N)·∏geomSumC` (the `1/a_N`-rescaled lattice gap) is conserved with a
    positive floor along the real irrational `e^{−1}` self-similar flow
    (`uniformContinuumFloor_concreteE`).  This is the DIALED toy realized in Lean; the
    REAL 4D flow's Λ is the residual.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9) — maximally adversarial

The RG-invariant `Λ = μ·exp(−1/(2β₀g²))` is a concrete CReal and its POSITIVITY is
TRIVIAL (`exp` is positive — `condensate_creal_nonneg`, the RED HERRING).  The
GENERATION — that the REAL 4D block-spin flow HAS this nonzero `Λ` as its RG-invariant
(the real mass gap) — is NOT constructed here.  Two facts pin the reduction:

  1. The self-similar STEP is proved unconditionally, but it is the step of the
     already-built condensate MODEL, and holds for the ideal (zero-defect) trajectory.
     The dimensionful conservation `rgScaleLambda_conserved` is CONDITIONAL on the
     matched spacing `hmatch`, which is the DIAL (`DimensionlessMarginTransmutation`'s
     `ε ≡ 0` self-similar flow), not a derivation for the real flow.

  2. The real flow's DEVIATION from this ideal self-similarity is the additive erosion
     `ε_k`, i.e. `SingleStepDefectBound.singleStep : realδ_k ≤ δ_model_k`
     (`RGFlowGapAssembly`).  So the constructive RG GENERATION of the real Λ reduces
     EXACTLY to `singleStep` — the same irreducible non-perturbative core (the
     interacting-measure / fusion-local-CLT input), NOT a new generation mechanism.

`rgScaleLambda_conserved` is a CONDITIONAL producer (open `mu`, `hmatch`); it inhabits
NONE of the guarded frontier bundles (`SingleStepDefectBound`, `TrueMarginRecursion*`,
`UniformSpacingFloor`, `Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`,
`FrontierDAG`).  No guarded bundle is inhabited; nothing is faked; the constructive
non-perturbative RG carries the essential-singularity KINEMATICS (self-similar Λ) but
the GENERATION of the real Λ is the foundational Clay substrate (the interacting
measure obeying the renormalon structure), reduced here to `singleStep`.  The 4D
Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over `CRealExp` / `ExpAdd` / `CondensateGeometricErosion` /
`DimensionlessMarginTransmutation`.  Every load-bearing declaration gated with
`#print axioms`; permitted output `propext` / `Quot.sound`.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.CondensateGeometricErosion
import YMGap.Continuum.DimensionlessMarginTransmutation
import YMGap.Constructive.ExpAdd
import YMGap.Constructive.ExpNegCongr

namespace YMGap.Continuum.RGInvariantScale

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.CondensateGeometric
open YMGap.Continuum.CodynamicCRealFlow

/-! ## 1. The essential-singularity ratio `ρ = exp(−c/(β₀A)) = exp(−6/11)` -/

/-- The condensate ratio exponent `c/(β₀A) = 6/11` is nonnegative. -/
theorem condRateExp_nonneg : (0 : Q') ≤ condRateExp := by decide

/-- **The self-similar RG ratio** `ρ = exp(−6/11) ∈ (0,1)` — the FIXED factor by
which the essential-singularity condensate scale is multiplied at each block-spin RG
step.  A genuine irrational CReal. -/
def rho : CReal := ExpNeg.expNeg condRateExp condRateExp_nonneg

/-- `ρ ≥ 0` (trivial — the exp-positivity red herring, at the ratio level). -/
theorem rho_nonneg : ExpPos.geRat rho 0 :=
  expNeg_geRat_zero condRateExp condRateExp_nonneg

/-! ## 2. The exponent recursion — one RG step adds the fixed ratio exponent -/

/-- **The condensate exponent recursion.**  `condExponent (k+1) ≃ condExponent k +
condRateExp`, i.e. `(6/11)(k+1+12) ≃ (6/11)(k+12) + (6/11)`.  Pure `Q'` algebra. -/
theorem condExponent_succ (k : Nat) :
    (condExponent (k + 1)).eqv (condExponent k + condRateExp) := by
  show (condRateExp * Q'.ofNat (k + 1 + condOffset)).eqv
      (condRateExp * Q'.ofNat (k + condOffset) + condRateExp)
  have hnat : k + 1 + condOffset = k + condOffset + 1 := by omega
  rw [hnat]
  -- ofNat (m+1) ≃ ofNat m + 1
  have e1 : (Q'.ofNat (k + condOffset + 1)).eqv (Q'.ofNat (k + condOffset) + 1) :=
    Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (k + condOffset) 1)
      (Q'.add_eqv_congr_left (Q'.ofNat (k + condOffset)) (Q'.ofNat 1) 1 (by decide))
  -- ρ_exp·ofNat(m+1) ≃ ρ_exp·(ofNat m + 1) ≃ ρ_exp·ofNat m + ρ_exp·1 ≃ ρ_exp·ofNat m + ρ_exp
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left condRateExp _ _ e1) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_add_eqv condRateExp (Q'.ofNat (k + condOffset)) 1) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv condRateExp)

/-! ## 3. THE EXACT SELF-SIMILAR RG STEP (PROVED, unconditional) -/

/-- **THE ESSENTIAL-SINGULARITY FACTOR IS EXACTLY SELF-SIMILAR UNDER ONE RG STEP.**

    condensateCReal (k+1)  ≃  condensateCReal k · ρ ,       ρ = exp(−6/11) ∈ (0,1).

The non-perturbative condensate scale `exp(−c/(β₀g_k²))` is multiplied by the FIXED
irrational ratio `ρ` at every block-spin step — the RG self-similarity that makes
`Λ = μ·condensate` a flow invariant (given the matched RG-scale growth `μ ↦ μ/ρ`).
Proof: the exponent recursion `condExponent_succ` fed through the exponential addition
law `e^{−(a+b)} ≃ e^{−a}·e^{−b}` (`expNeg_add_equiv`).  This is the concrete
`exp(−1/(2β₀g²))` RG kinematics the task asks to construct. -/
theorem condensate_selfSimilar_step (k : Nat) :
    CReal.Equiv (condensateCReal (k + 1))
      (CReal.mul (condensateCReal k) rho) := by
  have h1 : CReal.Equiv (condensateCReal (k + 1))
      (ExpNeg.expNeg (condExponent k + condRateExp)
        (Q'.zero_le_add _ _ (condExponent_nonneg k) condRateExp_nonneg)) :=
    expNeg_eqv_congr (condExponent_nonneg (k + 1)) _ (condExponent_succ k)
  have h2 : CReal.Equiv
      (ExpNeg.expNeg (condExponent k + condRateExp)
        (Q'.zero_le_add _ _ (condExponent_nonneg k) condRateExp_nonneg))
      (CReal.mul (condensateCReal k) rho) :=
    CReal.Equiv.symm
      (expNeg_add_equiv (condExponent k) condRateExp
        (condExponent_nonneg k) condRateExp_nonneg)
  exact CReal.Equiv.trans h1 h2

/-! ## 4. THE RG-INVARIANT DIMENSIONFUL SCALE `Λ_k = μ_k·exp(−1/(2β₀g_k²))` -/

/-- **THE RG-INVARIANT SCALE** at RG step `k`:

    rgScaleLambda μ k  =  μ_k · condensateCReal k  =  μ_k · exp(−c/(β₀g_k²)),

the RG scale `μ_k = 1/a_k` times the essential-singularity condensate factor — the
dimensional-transmutation invariant `Λ`.  `μ` is a free CReal RG-scale sequence; the
invariance (§5) requires the matched self-similar growth of `μ`. -/
def rgScaleLambda (mu : Nat → CReal) (k : Nat) : CReal :=
  CReal.mul (mu k) (condensateCReal k)

/-- **THE RG-INVARIANT `Λ` IS CONSERVED ALONG THE MATCHED FLOW (conditional).**

Given the matched self-similar RG-scale law `hmatch : ρ·μ_{k+1} ≃ μ_k` (the RG scale
`μ = 1/a` grows by exactly `1/ρ` per block step, cancelling the condensate's `ρ`
shrink), the dimensionful RG-invariant is conserved:

    rgScaleLambda μ k  ≃  rgScaleLambda μ (k+1) ,   ∀ k.

This IS dimensional transmutation for `Λ`: the RG scale `μ_k → ∞` and the
essential-singularity factor `exp(−c/β₀g_k²) → 0` at reciprocal rates, so their
product `Λ` stays fixed.  OPEN binders on `mu`, `hmatch`: a CONDITIONAL producer.
`hmatch` is the DIAL (the ideal `ε ≡ 0` self-similar trajectory of
`DimensionlessMarginTransmutation`); the REAL flow's deviation is the residual
`singleStep`. -/
theorem rgScaleLambda_conserved (mu : Nat → CReal)
    (hmatch : ∀ k, CReal.Equiv (CReal.mul rho (mu (k + 1))) (mu k)) (k : Nat) :
    CReal.Equiv (rgScaleLambda mu k) (rgScaleLambda mu (k + 1)) := by
  refine CReal.Equiv.symm ?_
  -- Λ_{k+1} = μ_{k+1}·cond_{k+1} ≃ μ_{k+1}·(cond_k·ρ)
  have hA : CReal.Equiv (rgScaleLambda mu (k + 1))
      (CReal.mul (mu (k + 1)) (CReal.mul (condensateCReal k) rho)) :=
    mul_congr_rightC (condensate_selfSimilar_step k)
  -- μ_{k+1}·(cond_k·ρ) ≃ (μ_{k+1}·ρ)·cond_k
  have hB : CReal.Equiv
      (CReal.mul (mu (k + 1)) (CReal.mul (condensateCReal k) rho))
      (CReal.mul (CReal.mul (mu (k + 1)) rho) (condensateCReal k)) :=
    mul_swap_rightC (mu (k + 1)) (condensateCReal k) rho
  -- μ_{k+1}·ρ ≃ ρ·μ_{k+1} ≃ μ_k
  have hAeq : CReal.Equiv (CReal.mul (mu (k + 1)) rho) (mu k) :=
    CReal.Equiv.trans (cmul_comm (mu (k + 1)) rho) (hmatch k)
  -- (μ_{k+1}·ρ)·cond_k ≃ μ_k·cond_k = Λ_k
  have hC : CReal.Equiv
      (CReal.mul (CReal.mul (mu (k + 1)) rho) (condensateCReal k))
      (rgScaleLambda mu k) :=
    CReal.mul_congr_left hAeq
  exact CReal.Equiv.trans hA (CReal.Equiv.trans hB hC)

/-- **The RG-invariant `Λ` is nonnegative when the RG scale is** — and its condensate
factor is nonnegative TRIVIALLY (`exp` positive).  This is the RED HERRING: `Λ ≥ 0`
(indeed `> 0` for `μ > 0`) is FREE; the mass gap is NOT this, it is that the REAL
flow's invariant EQUALS a nonzero `Λ` (§5, the residual). -/
theorem condensate_factor_nonneg (k : Nat) : ExpPos.geRat (condensateCReal k) 0 :=
  condensate_creal_nonneg k

/-! ## 5. NON-VACUITY of the mechanism (unconditional re-export) -/

/-- **THE RG-INVARIANT MECHANISM IS GENUINE, NOT VACUOUS.**  A conserved positive
RG-invariant EXISTS in Lean unconditionally: the dimensionless margin
`(1 − sep N)·∏geomSumC` — the `1/a_N`-rescaled lattice gap — is bounded below by a
single positive rational at EVERY scale `N` along the real irrational `e^{−1}`
self-similar CReal flow.  This is the DIALED transmutation toy realized (the exp-on-
CReal residual discharged via genuinely irrational separators); the REAL 4D flow's
`Λ` is the residual (§6). -/
theorem rgInvariant_mechanism_nonvacuous :
    ∃ c : Q', (0 : Q') < c ∧
      ∀ N, CReal.leEv (CReal.ofQ' c)
        (DimensionlessMarginTransmutation.dimMargin 1
          (CodynamicCRealFlow.concreteCRealFlowE 1).s N) :=
  DimensionlessMarginTransmutation.uniformContinuumFloor_concreteE

/-! ## 6. Honest verdict (AGENTS.md Rule 6 / Rule 9) -/

/-- **PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):**
  * `condExponent_succ` — one RG step adds the fixed ratio exponent `6/11`.
  * `condensate_selfSimilar_step` — the essential-singularity factor
    `exp(−c/β₀g_k²)` is EXACTLY self-similar: `condensateCReal (k+1) ≃
    condensateCReal k · ρ`, `ρ = exp(−6/11)` (via `expNeg_add_equiv`).
  * `rgScaleLambda_conserved` — the dimensionful RG-invariant
    `Λ_k = μ_k·exp(−c/β₀g_k²)` is CONSERVED along the matched self-similar RG-scale
    growth (CONDITIONAL on `hmatch`, the dial).
  * `condensate_factor_nonneg` — `Λ`'s condensate factor is nonneg TRIVIALLY (the red
    herring: `Λ > 0` as a number is free).
  * `rgInvariant_mechanism_nonvacuous` — a conserved positive RG-invariant EXISTS
    unconditionally (the dimensionless margin along the irrational `e^{−1}` flow).

**VERDICT — the constructive RG carries the essential-singularity KINEMATICS of `Λ`,
but the GENERATION of the REAL `Λ` reduces to `singleStep`.**  The RG-invariant
`Λ = μ·exp(−1/(2β₀g²))` is a concrete irrational CReal whose factor is self-similar
under one RG step (PROVED) and whose dimensionful value is conserved along the matched
self-similar flow (`rgScaleLambda_conserved`, conditional).  Its POSITIVITY is TRIVIAL
(`condensate_factor_nonneg` — `exp` is positive, the RED HERRING).  What is NOT
constructed, and what the mass gap needs:

  * the matched spacing `hmatch` is the DIAL — the ideal `ε ≡ 0` self-similar
    trajectory (`DimensionlessMarginTransmutation`), not the real flow;
  * the REAL flow's deviation from this ideal is the additive erosion `ε_k`, i.e.
    `SingleStepDefectBound.singleStep : realδ_k ≤ δ_model_k` (`RGFlowGapAssembly`),
    the interacting-measure / fusion-local-CLT input.

So the constructive non-perturbative RG generation IS `singleStep` — the SAME
irreducible core, NOT a genuinely different generation mechanism.  A dialed `Λ` (from
the toy self-similar seed) is NOT the real generation; the real 4D flow's `Λ` is the
foundational Clay substrate (the interacting field integral obeying the renormalon
structure), which the Lean-core library carries only as the KINEMATICS, with the
GENERATION reduced to `singleStep`.  `rgScaleLambda_conserved` is a CONDITIONAL
producer (open `mu`, `hmatch`); it inhabits NONE of the guarded frontier bundles.  No
guarded bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN. -/
theorem rgInvariantScale_honesty : True := trivial

end YMGap.Continuum.RGInvariantScale

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RGInvariantScale.condRateExp_nonneg
#print axioms YMGap.Continuum.RGInvariantScale.rho_nonneg
#print axioms YMGap.Continuum.RGInvariantScale.condExponent_succ
#print axioms YMGap.Continuum.RGInvariantScale.condensate_selfSimilar_step
#print axioms YMGap.Continuum.RGInvariantScale.rgScaleLambda_conserved
#print axioms YMGap.Continuum.RGInvariantScale.condensate_factor_nonneg
#print axioms YMGap.Continuum.RGInvariantScale.rgInvariant_mechanism_nonvacuous
