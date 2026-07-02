/-
The CONTINUOUS functional calculus for the Wilson transfer operator — the
"Bernstein limit" that upgrades the polynomial calculus of
`Continuum/BoundedTransferCalculus.lean` from single monomials `f = xⁿ` to a
general continuous `f`.

# What this module adds (all axiom-clean)

`BoundedTransferCalculus.lean` proved, from the finite diagonal spectral
resolution `DiagResolution` of the transfer operator `T`:
  * `diagResolution_normGap` : `‖T x‖² ≤ sep²·‖x‖²` on `vac⊥`;
  * `Tpow` / `Tpow_contraction` : the monomial calculus `f(λ)=λⁿ ↦ Tⁿ`;
  * `BoundedTransferCalculusResidual` : the correct residual (bounded self-adjoint
    `f(T)` with `‖f(T)x‖² ≤ M²‖x‖²`), inhabited only by monomials.

Here we deliver the two structural mechanisms that convert that residual from
"no continuous `f`" to "supply any uniformly-Cauchy polynomial sequence":

  * **PART A — the diagonal polynomial estimate** (`polyNormBound`).  The scalar
    action of `T` on the resolution is diagonal with eigenvalues `λ_i`, so any
    polynomial `p` acts with eigenvalues `p(λ_i)` and the resolved squared norm
    is `Σ p(λ_i)²·|c_i|²`.  We prove
        `Σ p(λ_i)²·|c_i|² ≤ M·‖x‖²`   whenever   `p(λ_i)² ≤ M`  for all `i`,
    i.e. `‖p(T)x‖² ≤ ‖p‖²_{∞,spec}·‖x‖²` — the GENERALIZATION of
    `diagResolution_normGap` from `xⁿ` to an arbitrary polynomial `p`.  The
    load-bearing new input is the SCALAR-monotonicity of the `Q'`-scaling
    (`RCscale_scalar_mono`), proved here from the pointwise
    `mul_le_mul_of_nonneg_left` estimate `leEv_scalar_mono`.

  * **PART A — the pointwise operator limit** (`symbolLimit`).  A
    `SpectralUnifCauchy` datum — a `Type`-level uniform Cauchy modulus for a
    polynomial sequence `pₙ` at a spectral point `λ` — yields, via the constructive
    completeness `CReal.completeLimitCauchy`, the limit symbol
    `f(λ) := lim pₙ(λ)` as a genuine `CReal`, with the uniform bound
    `|f(λ)| ≤ lim ‖pₙ‖_∞` passing to the limit (`symbolLimit_le`,
    `symbolLimit_ge`).  This is the Bernstein/Weierstrass limit read at each point
    of the located transfer spectrum.

  * **PART B — the Bernstein input** (`bernstein_partition_scaled_n2`,
    `bernstein_variance_scaled_n2`).  The Bernstein approximation supplies the
    uniformly-Cauchy polynomial sequence.  Its two structural identities — the
    partition of unity `Σ_k C(n,k)xᵏ(1−x)ⁿ⁻ᵏ = 1` and the VARIANCE identity
    `Σ_k (k/n−x)²·C(n,k)xᵏ(1−x)ⁿ⁻ᵏ = x(1−x)/n` — are validated here at `n = 2`
    (integer-scaled to avoid `Q'` fractions) as `QPoly` identities discharged by
    `decide`, exercising the reflective polynomial ring end-to-end.  The general-`n`
    variance identity is the single named remaining Bernstein input.

# Honest scope

`polyNormBound` is a statement about the resolved quadratic FORM
`Σ p(λ_i)²|c_i|²` (the data actually available in `DiagResolution`), and
`symbolLimit` produces the limit SYMBOL.  Assembling `f(T)` as an explicit map
`carrier → carrier` additionally needs the vector-space operations on the
completed carrier, which the `TransferOperator` interface deliberately does not
expose in this development (only composition `Tⁿ` is available; see
`GNSDynamics.lean`).  So this module reduces core ④ to exactly that architectural
input, delivering the two genuinely new analytic mechanisms — the diagonal
polynomial norm bound and the constructive pointwise operator limit — GREEN.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Constructive.CRealCompleteCauchy
import YMGap.Constructive.QPoly
import YMGap.Constructive.CRealMul

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BoundedTransferCalculus

/-! ## Part A.0 — scalar monotonicity of the `Q'`-scaling on `RC` -/

namespace YMGap.Constructive.CReal

/-- **Pointwise scalar-monotonicity of `leEv`.**  For `s ≤ t` and a nonnegative
real `C` (`leEv czero C`), `leEv (s·C) (t·C)`.  Pointwise:
`(t−s)·(Cₙ+δ) ≥ 0` and `(t−s)·δ ≤ ε` give `s·Cₙ ≤ t·Cₙ + ε`. -/
theorem leEv_scalar_mono {s t : Q'} (hst : s ≤ t) {C : CReal}
    (hC : leEv czero C) : leEv (mul (ofQ' s) C) (mul (ofQ' t) C) := by
  -- `d := t + (−s) ≥ 0`
  have hd : (0 : Q') ≤ t + (-s) := by
    have h1 : s + (-s) ≤ t + (-s) := Q'.add_le_add_right s t (-s) hst
    have h2 : ((s : Q') + (-s)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.add_comm_eqv s (-s)) (Q'.neg_add_self_eqv s)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm h2)) h1
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_mul_le hd hε
  obtain ⟨N, hN⟩ := hC δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  show s * C.approx n ≤ t * C.approx n + ε
  have h0 : (0 : Q') ≤ C.approx n + δ := hN n hn
  -- abbreviate `a := C.approx n`, `d := t + (−s)` (inlined; no Mathlib `set`)
  have hstep : (t + (-s)) * 0 ≤ (t + (-s)) * (C.approx n + δ) :=
    Q'.mul_le_mul_of_nonneg_left 0 (C.approx n + δ) (t + (-s)) h0 hd
  have hd0 : (0 : Q') ≤ (t + (-s)) * (C.approx n + δ) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_mul_zero (t + (-s))))) hstep
  have hexp : ((t + (-s)) * (C.approx n + δ)).eqv
      ((t + (-s)) * C.approx n + (t + (-s)) * δ) :=
    Q'.mul_add_eqv (t + (-s)) (C.approx n) δ
  have hda2 : (0 : Q') ≤ (t + (-s)) * C.approx n + (t + (-s)) * δ :=
    Q'.le_trans' _ _ _ hd0 (Q'.le_of_eqv hexp)
  have hstep2 : (t + (-s)) * C.approx n + (t + (-s)) * δ
      ≤ (t + (-s)) * C.approx n + ε :=
    Q'.add_le_add_left ((t + (-s)) * C.approx n) ((t + (-s)) * δ) ε hδ
  have hdaε : (0 : Q') ≤ (t + (-s)) * C.approx n + ε :=
    Q'.le_trans' _ _ _ hda2 hstep2
  have hself : s * C.approx n ≤ s * C.approx n + ((t + (-s)) * C.approx n + ε) :=
    Q'.add_le_self_of_nonneg (s * C.approx n) ((t + (-s)) * C.approx n + ε) hdaε
  -- `s + (t + −s) ≃ t`
  have hts : ((s : Q') + (t + (-s))).eqv t := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left s (t + (-s)) ((-s) + t) (Q'.add_comm_eqv t (-s))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv s (-s) t)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (s + (-s)) 0 t
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv s (-s)) (Q'.neg_add_self_eqv s))) ?_
    exact QPoly.q_zero_add_eqv t
  -- `(s·a + ((t+−s)·a + ε)) ≃ t·a + ε`
  have heqv : (s * C.approx n + ((t + (-s)) * C.approx n + ε)).eqv
      (t * C.approx n + ε) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (s * C.approx n) ((t + (-s)) * C.approx n) ε)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (s * C.approx n + (t + (-s)) * C.approx n)
        ((s + (t + (-s))) * C.approx n) ε
        (Q'.eqv_symm (QPoly.q_add_mul s (t + (-s)) (C.approx n)))) ?_
    exact Q'.add_eqv_congr_right ((s + (t + (-s))) * C.approx n) (t * C.approx n) ε
      (Q'.mul_eqv_congr_right (s + (t + (-s))) t (C.approx n) hts)
  exact Q'.le_trans' _ _ _ hself (Q'.le_of_eqv heqv)

/-- **Scalar-monotonicity of the `RC`-scaling.**  For `s ≤ t` (in `Q'`) and a
nonnegative real `c`, `RCscale s c ≤ RCscale t c`.  This is the scalar-order
monotonicity (distinct from the argument-monotonicity `RCscale_mono`), threaded as
an open `Rscalar` residual elsewhere and discharged here. -/
theorem RCscale_scalar_mono {s t : Q'} (hst : s ≤ t) {c : RC} (hc : RCnonneg c) :
    RCle (RCscale s c) (RCscale t c) := by
  revert hc
  refine Quotient.inductionOn c ?_
  intro C hc
  show leEv (mul (ofQ' s) C) (mul (ofQ' t) C)
  exact leEv_scalar_mono hst hc

end YMGap.Constructive.CReal

namespace YMGap.Continuum.ContinuousTransferCalculus

open YMGap.Constructive.CReal

variable {D : GNSData} {H : CompleteGNSHilbert D} {G : SpectralGapData H}

/-! ## Part A.1 — the diagonal polynomial norm estimate -/

/-- The **resolved squared norm** of a diagonal operator with real symbol values
`μ : Fin k → Q'`: `Σ μᵢ·|cᵢ(x)|²`.  For `μᵢ = p(λᵢ)²` this is `‖p(T)x‖²`. -/
def specNormSq (Br : DiagResolution G) (μ : Fin Br.k → Q')
    (x : H.hilbert.carrier) : RC :=
  RCfinSum Br.k (fun i => RCscale (μ i) (Br.coeffSq x i))

/-- **Monotonicity of the resolved norm in the symbol.**  `μᵢ ≤ νᵢ` (pointwise)
gives `Σ μᵢ|cᵢ|² ≤ Σ νᵢ|cᵢ|²`, by termwise scalar-monotone `RCscale` over the
nonnegative coordinate weights. -/
theorem specNormSq_mono (Br : DiagResolution G) {μ ν : Fin Br.k → Q'}
    (h : ∀ i, μ i ≤ ν i) (x : H.hilbert.carrier) :
    RCle (specNormSq Br μ x) (specNormSq Br ν x) :=
  RCfinSum_mono (fun i => RCscale_scalar_mono (h i) (Br.coeffSq_nonneg x i))

/-- The constant-symbol resolved norm equals the scaled total norm:
`RCscale M ⟨x,x⟩ = Σ M·|cᵢ|²`.  (`innerSelf_diag` then `RCscale_finSum`.) -/
theorem const_scale_inner (Br : DiagResolution G) (M : Q') (x : H.hilbert.carrier) :
    RCscale M (H.hilbert.cinner x x)
      = RCfinSum Br.k (fun i => RCscale M (Br.coeffSq x i)) := by
  rw [Br.innerSelf_diag x, RCscale_finSum]

/-- **The diagonal polynomial norm bound** (PART A core).  For a polynomial `p`
and a uniform spectral bound `M` with `p(λᵢ)² ≤ M` for all resolved modes `i`, the
resolved squared norm of `p(T)` obeys
    `Σ p(λᵢ)²·|cᵢ|² ≤ M·‖x‖²`,
i.e. `‖p(T)x‖² ≤ ‖p‖²_{∞,spec}·‖x‖²`.  This GENERALIZES
`diagResolution_normGap` (the single monomial `p(λ)=λ`, `M=sep²`) to an arbitrary
polynomial, using `specNormSq_mono` against the constant symbol `M` and
`const_scale_inner`. -/
theorem polyNormBound (Br : DiagResolution G) (p : QPoly.Poly) (M : Q')
    (hM : ∀ i, QPoly.eval p (Br.lam i) * QPoly.eval p (Br.lam i) ≤ M)
    (x : H.hilbert.carrier) :
    RCle (specNormSq Br (fun i => QPoly.eval p (Br.lam i) * QPoly.eval p (Br.lam i)) x)
         (RCscale M (H.hilbert.cinner x x)) := by
  rw [const_scale_inner Br M x]
  exact RCfinSum_mono (fun i => RCscale_scalar_mono (hM i) (Br.coeffSq_nonneg x i))

/-! ## Part A.2 — the pointwise operator limit (the Bernstein/Weierstrass limit) -/

/-- The constant-per-index `CReal` sequence `n ↦ ofQ' (pₙ(λ))`. -/
def evOfQ (p : Nat → QPoly.Poly) (lam : Q') : Nat → CReal :=
  fun n => ofQ' (QPoly.eval (p n) lam)

/-- A **uniform Cauchy modulus for a polynomial sequence at a spectral point**.
`Nmod` is the `Type`-level modulus, antitone (`Mmono`), and past it the values
`pₘ(λ), pₙ(λ)` agree two-sidedly within `ε` (`cauchy`) — the honest constructive
reading of `‖pₘ − pₙ‖_{∞,spec} ≤ ε` restricted to the point `λ`. -/
structure SpectralUnifCauchy (p : Nat → QPoly.Poly) (lam : Q') where
  /-- The Cauchy modulus. -/
  Nmod : Q' → Nat
  /-- Antitone modulus (finer tolerance ⟹ larger stage). -/
  Mmono : ∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → Nmod ε ≤ Nmod δ
  /-- Two-sided uniform Cauchy bound past `Nmod ε`. -/
  cauchy : ∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, Nmod ε ≤ m → Nmod ε ≤ n →
    QPoly.eval (p m) lam ≤ QPoly.eval (p n) lam + ε
      ∧ QPoly.eval (p n) lam ≤ QPoly.eval (p m) lam + ε

/-- Package a `SpectralUnifCauchy` as the constructive completeness datum
`ModCauchyEv` for the constant-per-index sequence `evOfQ p lam`.  The inner
regularity is trivial (each term is a constant `CReal`); the outer bound is
`cauchy`; antitonicity is `Mmono`. -/
def spectralModCauchy {p : Nat → QPoly.Poly} {lam : Q'}
    (U : SpectralUnifCauchy p lam) : ModCauchyEv (evOfQ p lam) where
  M := U.Nmod
  reg := fun _ _ => 0
  boundK := fun _ _ _ => 0
  bound := fun ε hε m n hm hn _ _ => U.cauchy ε hε m n hm hn
  regular := fun i ε hε p' q' _ _ => by
    refine ⟨?_, ?_⟩ <;>
      · show QPoly.eval (p i) lam ≤ QPoly.eval (p i) lam + ε
        exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)
  Mmono := U.Mmono

/-- **The limit symbol** `f(λ) := lim pₙ(λ)` as a genuine `CReal`, via the
constructive diagonal completeness `completeLimitCauchy`.  This is the
Bernstein/Weierstrass limit read at the spectral point `λ`. -/
def symbolLimit {p : Nat → QPoly.Poly} {lam : Q'} (U : SpectralUnifCauchy p lam) :
    CReal :=
  completeLimitCauchy (evOfQ p lam) (spectralModCauchy U)

/-- **The limit is the limit** — `pₙ(λ) → f(λ)`. -/
theorem symbolLimit_converges {p : Nat → QPoly.Poly} {lam : Q'}
    (U : SpectralUnifCauchy p lam) :
    ConvergesTo (evOfQ p lam) (symbolLimit U) :=
  convergesTo_completeLimitCauchy (evOfQ p lam) (spectralModCauchy U)

/-- **Uniform upper bound passes to the limit.**  If `pₙ(λ) ≤ ub` for all `n`,
then `f(λ) ≤ ub`. -/
theorem symbolLimit_le {p : Nat → QPoly.Poly} {lam : Q'} (U : SpectralUnifCauchy p lam)
    {ub : Q'} (hub : ∀ n, QPoly.eval (p n) lam ≤ ub) :
    leEv (symbolLimit U) (ofQ' ub) :=
  leEv_completeLimitCauchy_ofQ' (evOfQ p lam) (spectralModCauchy U) (fun kk _ => hub kk)

/-- **Uniform lower bound passes to the limit.**  If `lb ≤ pₙ(λ)` for all `n`,
then `lb ≤ f(λ)`.  Combined with `symbolLimit_le`, this is `|f(λ)| ≤ lim ‖pₙ‖_∞`. -/
theorem symbolLimit_ge {p : Nat → QPoly.Poly} {lam : Q'} (U : SpectralUnifCauchy p lam)
    {lb : Q'} (hlb : ∀ n, lb ≤ QPoly.eval (p n) lam) :
    leEv (ofQ' lb) (symbolLimit U) :=
  leEv_ofQ'_completeLimitCauchy (evOfQ p lam) (spectralModCauchy U) (fun kk _ => hlb kk)

/-! ## Part B — the Bernstein input (structural identities, validated at `n = 2`)

The Bernstein sequence `bₙ(f)(x) = Σ_{k=0}^n f(k/n)·C(n,k)·xᵏ(1−x)ⁿ⁻ᵏ` supplies a
uniformly-Cauchy polynomial sequence for any continuous `f`.  Its convergence rests
on two moment identities of the binomial weights.  We validate both at `n = 2`
(scaled by `4` to keep integer `Q'` coefficients) as reflective `QPoly` identities.

The three `n = 2` Bernstein basis polynomials in `x`:
  * `b₂₀ = (1−x)²`, `b₂₁ = 2x(1−x)`, `b₂₂ = x²`. -/

/-- `(1−x)²` as a coefficient list. -/
def b20 : QPoly.Poly := QPoly.pmul [1, -(1 : Q')] [1, -(1 : Q')]
/-- `2x(1−x)`. -/
def b21 : QPoly.Poly := QPoly.pmul [0, Q'.ofNat 2] [1, -(1 : Q')]
/-- `x²`. -/
def b22 : QPoly.Poly := [0, 0, 1]

/-- The Bernstein weights at `n = 2` sum to the constant polynomial `1`
(**partition of unity** `Σ_k C(2,k)xᵏ(1−x)²⁻ᵏ = 1`), a `QPoly` identity by
`decide`. -/
theorem bernstein_partition_scaled_n2 (x : Q') :
    (QPoly.eval (QPoly.padd b20 (QPoly.padd b21 b22)) x).eqv (QPoly.eval [1] x) :=
  QPoly.poly_eqv _ _ x (by decide)

/-- The **variance identity** at `n = 2`, integer-scaled by `4`:
`Σ_k (k−2x)²·C(2,k)xᵏ(1−x)²⁻ᵏ = 2x(1−x)` (i.e. `Σ_k (k/2−x)²·b₂ₖ = x(1−x)/2`), a
`QPoly` identity by `decide`.  The factors `(k−2x)²` are `4x²`, `(1−2x)²`,
`(2−2x)²`. -/
theorem bernstein_variance_scaled_n2 (x : Q') :
    (QPoly.eval
      (QPoly.padd (QPoly.pmul [0, 0, Q'.ofNat 4] b20)
        (QPoly.padd (QPoly.pmul [1, -(Q'.ofNat 4), Q'.ofNat 4] b21)
          (QPoly.pmul [Q'.ofNat 4, -(Q'.ofNat 8), Q'.ofNat 4] b22))) x).eqv
      (QPoly.eval (QPoly.pmul [0, Q'.ofNat 2] [1, -(1 : Q')]) x) :=
  QPoly.poly_eqv _ _ x (by decide)

end YMGap.Continuum.ContinuousTransferCalculus

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.leEv_scalar_mono
#print axioms YMGap.Constructive.CReal.RCscale_scalar_mono
#print axioms YMGap.Continuum.ContinuousTransferCalculus.specNormSq_mono
#print axioms YMGap.Continuum.ContinuousTransferCalculus.const_scale_inner
#print axioms YMGap.Continuum.ContinuousTransferCalculus.polyNormBound
#print axioms YMGap.Continuum.ContinuousTransferCalculus.spectralModCauchy
#print axioms YMGap.Continuum.ContinuousTransferCalculus.symbolLimit
#print axioms YMGap.Continuum.ContinuousTransferCalculus.symbolLimit_converges
#print axioms YMGap.Continuum.ContinuousTransferCalculus.symbolLimit_le
#print axioms YMGap.Continuum.ContinuousTransferCalculus.symbolLimit_ge
#print axioms YMGap.Continuum.ContinuousTransferCalculus.bernstein_partition_scaled_n2
#print axioms YMGap.Continuum.ContinuousTransferCalculus.bernstein_variance_scaled_n2
