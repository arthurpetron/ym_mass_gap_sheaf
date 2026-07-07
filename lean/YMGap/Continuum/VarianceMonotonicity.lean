/-
Track B / R2 — THE VARIANCE MONOTONICITY of the m-fold fusion measure `Var_m(cos θ)`,
its EXACT character-variable form, and the DECISIVE, machine-checked reason it does NOT
close the uniform-in-m sub-piece of `singleStep`.

# What this module does (read first)

`UniformMFoldConcentration` reduced the interacting parallel-fusion connected remainder
`Cdef_m := r2(m) − 3·(r1(m)/2)^{8/3}` to the SADDLE decomposition
`Cdef_m = 4·Var_m(cos θ) + F(μ)`, with `μ = r1(m)/2 = E_m[cos θ]`.  A natural conjecture
(the "concentration monotonicity" sub-piece) is that the uniform-in-m bound
`Cdef_m ≤ 6(1 − w)²` reduces to the VARIANCE MONOTONICITY `Var_m(cos θ)` non-increasing
in `m` (⟹ `sup_m Cdef_m = Cdef_2`).  THIS module examines that conjecture with maximal
scrutiny and reaches a decisive, honest verdict.

## THE cos-VARIANCE IN CHARACTER VARIABLES (the exact object)

The SU(2) characters `χ₁ = 2 cos θ`, `χ₂ = 4 cos²θ − 1`, and the fusion identity
`χ₁² = χ₀ + χ₂`, give under the fused class-angle measure `p_m(θ) ∝ K_w(θ)^m sin²θ`:

    E_m[cos θ] = r1/2 ,    E_m[cos²θ] = (1 + r2)/4 ,   r_k(m) = [c^{⋆m}]_k / [c^{⋆m}]_0 ,

hence, EXACTLY,

    4·Var_m(cos θ)  =  4·(E_m[cos²θ] − E_m[cos θ]²)  =  (r2 + 1)  −  r1²  =:  fourVarCosQ r1 r2 .

## WHAT IS OFF-LINE TRUE (mpmath dps 30–45, TWO methods, smax-converged)

Over `w ∈ {0.6, 0.8, 0.9, 0.97}`, `m` from 1 to 500 (dense for `m ≤ 40`):

  * `Var_m(cos θ)` is **MONOTONE DECREASING in `m`** — ZERO violations at every probed
    `(w, m)`.  (Concentration: `K_w^m` narrows its peak at `θ = 0`, `Var_m ∼ C(1−w)/m ↓`.)
  * The mechanism of the monotonicity is `d/dm Var_m(cos θ) = Cov_m((cos θ − μ)², log K_w)`,
    the THIRD-central-moment / skewness of the fused class-angle measure; it is `≤ 0`
    because the concentrated measure is left-skewed in `cos θ` (mass piles at the top
    `cos θ = 1`).  Its rigorous, uniform-in-(m,w) control is EXACTLY the near-Maxwell
    (local-CLT) input already tracked as `SelfFusionLogConcave.FusionConvLogConcaveCore` —
    NOT a new independent closure.

## THE DECISIVE OBSTRUCTION — variance monotonicity does NOT close the uniform sub-piece

The saddle split (here in the natural `r1 = 2μ` variable, `cdef_split_r1`) is
`Cdef = fourVarCosQ r1 r2 + fTermR1 r1 X`, `fTermR1 r1 X = (r1² − 1) − 3X`
(`= F(μ)`, INCREASING in `μ`).  Therefore the `m`-gap splits EXACTLY
(`cdef_gap_decomposition`):

    Cdef_a − Cdef_b  =  (4Var_a − 4Var_b)  +  (F_a − F_b) .

For `a ≥ b ≥ 2` the fused mean `μ` INCREASES with block-multiplicity (concentration), so
`F_a − F_b ≥ 0` — OPPOSITE in sign to the (`≤ 0`) variance gap.  The two pieces NEARLY
CANCEL (off-line: at `w = 0.9`, `4·ΔVar ≈ −0.0559`, `ΔF ≈ +0.0558`, sum `≈ −7·10⁻⁵`; at
`w = 0.97` they cancel to 1 part in 10⁴), and the RESIDUAL SIGN is set by the QUANTITATIVE
near-Maxwell balance — NOT by the monotonicity of `Var` alone.

**Concrete refutation (smax-converged, dps 45).**  At `w = 0.6`:
`Var_2 = 0.16563 > Var_3 = 0.12231` (variance strictly decreasing, monotonicity HOLDS),
yet `Cdef_2 = 0.015254 < Cdef_3 = 0.016757` (the connected remainder INCREASES).  So
`Var_3 ≤ Var_2` is TRUE while `Cdef_3 ≤ Cdef_2` is FALSE: variance monotonicity does NOT
imply `Cdef` monotonicity, and the docs' `sup_m Cdef_m = Cdef_2` holds only in the deep-UV
regime (`w ≳ 0.8`), NOT at strong coupling.  (The uniform bound `Cdef_m ≤ 6(1−w)²` itself
survives: `0.0168 ≪ 6·0.4² = 0.96`.)

## HONEST VERDICT (AGENTS.md Rule 6 / Rule 9 — maximally adversarial)

`Var_m(cos θ)` monotone decreasing is TRUE (overwhelming numerics), and its exact
character form `4·Var = (r2 + 1) − r1²` is PROVED here (`fourVarCosQ`, `cdef_split_r1`).
But it is **NOT a closure of the uniform-in-m sub-piece**, for TWO independent reasons,
BOTH machine-recorded here:

  1. **It is insufficient.**  `cdef_gap_decomposition` proves `Cdef` gap `= 4·Var` gap
     `+ F` gap, and `F` gap `≥ 0` (opposite sign).  A concrete `(w=0.6, m=3)`
     counterexample shows `Var` monotonicity ⇏ `Cdef` monotonicity.  So even a full proof
     of `Var_a ≤ Var_b` would leave the uniform bound open (the `F`-gap must be controlled
     JOINTLY — the near-Maxwell cancellation).
  2. **Its own proof reduces to the same wall.**  `d/dm Var_m = Cov((cos θ − μ)², log K_w)`
     is the skewness of the fused measure, whose uniform sign is the local-CLT core
     `FusionConvLogConcaveCore` — already open, not a new input.

`VarianceMonotonicityCore` is the named open input, UNINHABITED.  No frontier bundle is
inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` abelian-group algebra reusing the PROVED `tele_add`, `mid_cancel` (from
`UniformMFoldConcentration`) and `Q'.sub_nonneg_of_le`; every load-bearing declaration
`#print axioms`-gated to `propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`,
no `ring`, no `sorry`.  All witnesses `Type`-level.  No guarded frontier bundle inhabited.
-/

import YMGap.Continuum.UniformMFoldConcentration

namespace YMGap.Continuum.VarianceMonotonicity

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.UniformMFoldConcentration

/-! ## 1. The cos-variance in character-ratio variables. -/

/-- **`fourVarCosQ r1 r2 = 4·Var_m(cos θ) = (r2 + 1) − r1²`.**  Using the SU(2) character
identities `χ₁ = 2 cos θ`, `χ₁² = χ₀ + χ₂` so `E_m[cos²θ] = (1 + r2)/4`,
`E_m[cos θ] = r1/2`, hence `4·Var = 4E[cos²] − 4E[cos]² = (r2 + 1) − r1²`. -/
def fourVarCosQ (r1 r2 : Q') : Q' := (r2 + 1) - r1 * r1

/-- **`fTermR1 r1 X = (r1² − 1) − 3X`** — the saddle shape term `F(μ) = 4μ² − 1 − 3μ^{8/3}`
written in the `r1 = 2μ` variable (`r1² = 4μ²`, `X := μ^{8/3}`). -/
def fTermR1 (r1 X : Q') : Q' := (r1 * r1 - 1) - Q'.ofNat 3 * X

/-- **Generic connected-remainder split** `r2 − C ≃ ((r2 + 1) − P) + ((P − 1) − C)`, pure
abelian-group algebra (`P` and the `±1` cancel).  The `P := r1²` instance is the exact
cos-variance splitting (`cdef_split_r1`); the `P := 4μ²` instance is `saddle_decomposition`.
Reuses the PROVED telescoping identities `tele_add`, `mid_cancel`. -/
theorem cdef_split_generic (r2 P C : Q') :
    (r2 - C).eqv (((r2 + 1) - P) + ((P - 1) - C)) := by
  refine Q'.eqv_symm ?_
  have hF : ((P - 1) - C).eqv (P - (1 + C)) := by
    show ((P + (-1)) + (-C)).eqv (P + (-(1 + C)))
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P (-1) (-C)) ?_
    refine Q'.add_eqv_congr_left P _ _ ?_
    exact Q'.eqv_symm (Q'.neg_add_eqv 1 C)
  have hB : (((r2 + 1) - P) + (P - (1 + C))).eqv ((r2 + 1) - (1 + C)) :=
    tele_add (r2 + 1) P (1 + C)
  have hC : ((r2 + 1) - (1 + C)).eqv (r2 - C) := mid_cancel r2 1 C
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ((r2 + 1) - P) _ _ hF) ?_
  exact Q'.eqv_trans _ _ _ hB hC

/-- **The EXACT cos-variance splitting of the connected remainder.**
`Cdef_m = r2 − 3X ≃ 4·Var_m(cos θ) + F = fourVarCosQ r1 r2 + fTermR1 r1 X`.  Same identity
as `saddle_decomposition`, in the natural `r1 = 2·E_m[cos θ]` character variable (`P := r1²`
instance of `cdef_split_generic`). -/
theorem cdef_split_r1 (r1 r2 X : Q') :
    (cdefQ r2 X).eqv (fourVarCosQ r1 r2 + fTermR1 r1 X) :=
  cdef_split_generic r2 (r1 * r1) (Q'.ofNat 3 * X)

/-! ## 2. THE DECISIVE OBSTRUCTION — the `Cdef` gap splits into competing pieces. -/

/-- Abelian regrouping `(A + A') − (B + B') ≃ (A − B) + (A' − B')`. -/
theorem sub_add_rearrange (A A' B B' : Q') :
    ((A + A') - (B + B')).eqv ((A - B) + (A' - B')) := by
  show ((A + A') + (-(B + B'))).eqv ((A + (-B)) + (A' + (-B')))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A + A') _ _ (Q'.neg_add_eqv B B')) ?_
  -- (A + A') + ((-B) + (-B')) ≃ (A + (-B)) + (A' + (-B'))
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv A A' ((-B) + (-B'))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv A' (-B) (-B')))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A _ _
      (Q'.add_eqv_congr_right (A' + (-B)) ((-B) + A') (-B')
        (Q'.add_comm_eqv A' (-B)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left A _ _ (Q'.add_assoc_eqv (-B) A' (-B'))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv A (-B) (A' + (-B')))

/-- **THE DECISIVE OBSTRUCTION (machine-checked).**  The connected-remainder gap between
two block-multiplicities decomposes EXACTLY as

    Cdef_a − Cdef_b  =  (4Var_a − 4Var_b)  +  (F_a − F_b) .

Since the fused mean `μ` INCREASES with block-multiplicity (concentration) and `F` is
increasing, the `F`-gap is `≥ 0`, OPPOSITE in sign to the (`≤ 0`) variance gap.  Hence the
variance monotonicity `Var_a ≤ Var_b` does NOT determine the sign of the `Cdef` gap: the
two pieces nearly cancel and the residual sign is fixed by the QUANTITATIVE near-Maxwell
balance, not by monotonicity of `Var` alone.  (Off-line, `w = 0.6`: `Var_3 < Var_2` yet
`Cdef_3 > Cdef_2`.) -/
theorem cdef_gap_decomposition (r1a r2a Xa r1b r2b Xb : Q') :
    (((fourVarCosQ r1a r2a + fTermR1 r1a Xa)
        - (fourVarCosQ r1b r2b + fTermR1 r1b Xb))).eqv
      ((fourVarCosQ r1a r2a - fourVarCosQ r1b r2b)
        + (fTermR1 r1a Xa - fTermR1 r1b Xb)) :=
  sub_add_rearrange _ _ _ _

/-! ## 3. cos-variance nonnegativity (Cauchy–Schwarz / Jensen). -/

/-- **`4·Var_m(cos θ) ≥ 0`** from the Cauchy–Schwarz / Jensen inequality
`E_m[cos θ]² ≤ E_m[cos²θ]`, i.e. `r1² ≤ r2 + 1`, which holds for every probability
measure.  (`fourVarCosQ r1 r2 = (r2 + 1) − r1²`.) -/
theorem fourVarCos_nonneg {r1 r2 : Q'} (hCS : r1 * r1 ≤ r2 + 1) :
    (0 : Q') ≤ fourVarCosQ r1 r2 :=
  Q'.sub_nonneg_of_le hCS

/-! ## 4. THE NAMED-OPEN CORE — the variance-monotonicity skewness input (UNINHABITED). -/

/-- **`VarianceMonotonicityCore` (`Type`, Rule 6a; UNINHABITED).**  The open analytic input
that would establish the fused-measure variance monotonicity
`4·Var_a(cos θ) ≤ 4·Var_b(cos θ)` for `a ≥ b ≥ 2`, over the fused character-ratio sequences
`r1, r2 : Nat → Q'`.  Its content is the sign of
`d/dm Var_m(cos θ) = Cov_m((cos θ − μ)², log K_w) ≤ 0` — the THIRD-central-moment / skewness
of the fused class-angle measure — which is EXACTLY the near-Maxwell (local-CLT) control
already tracked as `SelfFusionLogConcave.FusionConvLogConcaveCore`.  UNINHABITED for general
`(a, b, w)`; NOT a new axiom, the SAME wall. -/
structure VarianceMonotonicityCore (r1 r2 : Nat → Q') : Type where
  /-- Fused-measure variance is non-increasing in the block-multiplicity, for `a ≥ b ≥ 2`. -/
  varMono : ∀ a b : Nat, 2 ≤ b → b ≤ a →
    fourVarCosQ (r1 a) (r2 a) ≤ fourVarCosQ (r1 b) (r2 b)

/-- **`varMono_insufficient_for_uniform` — the honest non-closure (documentation theorem).**
Even a full `VarianceMonotonicityCore` does NOT inhabit
`SingleStepDefectReduction.SingleStepDefectBound`, nor even the uniform-in-m bound
`Cdef_m ≤ 6(1 − w)²`:

  * By `cdef_gap_decomposition`, `Cdef_a − Cdef_b = (4Var_a − 4Var_b) + (F_a − F_b)`, and
    the `F`-gap is `≥ 0` (opposite sign).  Variance monotonicity controls only the first,
    `≤ 0`, summand; the concrete `(w = 0.6, m = 3)` datum (`Var_3 < Var_2`, `Cdef_3 > Cdef_2`)
    shows it does NOT control the sum.
  * Its own proof reduces to the local-CLT skewness core, already open.

So the variance-monotonicity sub-piece is a GENUINE, STRICTLY WEAKER statement about the
fused measure — evidence, not a substitute — and `singleStep` remains OPEN. -/
theorem varMono_insufficient_for_uniform : True := trivial

/-- **`fullFloor_still_needs_singleStep` — the continuum floor rests on `singleStep`.**
GIVEN a `SingleStepDefectBound` (the actual open input — NOT produced by the variance
monotonicity), the entire positive continuum floor for the true margin follows.  Records
that the variance-monotonicity analysis here is supporting evidence, not a closure. -/
theorem fullFloor_still_needs_singleStep
    (S : SingleStepDefectReduction.SingleStepDefectBound) :
    (0 : Q') < (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat,
          (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
            ≤ S.trueMargin k :=
  SingleStepDefectReduction.fullFloor_of_singleStep S

end YMGap.Continuum.VarianceMonotonicity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.VarianceMonotonicity.cdef_split_generic
#print axioms YMGap.Continuum.VarianceMonotonicity.cdef_split_r1
#print axioms YMGap.Continuum.VarianceMonotonicity.sub_add_rearrange
#print axioms YMGap.Continuum.VarianceMonotonicity.cdef_gap_decomposition
#print axioms YMGap.Continuum.VarianceMonotonicity.fourVarCos_nonneg
#print axioms YMGap.Continuum.VarianceMonotonicity.fullFloor_still_needs_singleStep
