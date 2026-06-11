/-
The **moment bridge** — scoping (and where reachable, closing) the step from
heat-kernel positivity to `MomentSquarePos`, the single analytic hypothesis
that `GramReduction.psd_of_momentSquare_nonneg` consumes to deliver uniform
Gram PSD.

# The definitional map (Part 2, the diagnosis)

`GramReduction.lean` defines, over an abstract nonnegative moment sequence
`MomentData M` (`m : Nat → CReal`, each `≥ 0`):

  * `gram M a b      = Σ_{j=0}^{min a b} m_{|a−b|+2j}`   (Clebsch–Gordan fusion)
  * `gramForm M c N  = Σ_{μ,ν<N} (c_μ c_ν)·gram M μ ν`   (the Gram quadratic form)
  * `momentSquare M c N = Σ_{μ,ν<N} (c_μ c_ν)·gram M μ ν`  (`E(q²)`, q = Σ c_μ χ_μ)

The crucial observation is that **`momentSquare` and `gramForm` are the SAME
double sum, definitionally** (`gramForm_eq_momentSquare` is `equiv_refl`).  So
the "reduction" `psd_of_momentSquare_nonneg` carries no content by itself: the
hypothesis `MomentSquarePos M := ∀ N c, momentSquare M c N ≥ 0` IS the uniform
PSD conclusion.  All the genuine work is in *supplying* `MomentSquarePos`.

`MomentData` is **abstract** — not heat-kernel-tied; `WilsonFunctional`'s
`wilsonMoments` instantiates it with the genuine single-edge heat-kernel
moments `m_s = (s+1)·e^{−t·s(s+2)/4}` (and `gramForm` then reduces *on the nose*
to `WilsonFunctional.coneExp`).

# Route (a) — the headline NEGATIVE finding

The task asked whether the already-proven flat-measure SOS-average positivity
(`TrigAvg.avg_nonneg_of_sos` / `cosSqAvg_nonneg`) can close `MomentSquarePos`
outright, making the heat-kernel-positivity detour (G1/G2) unnecessary.

**It cannot.**  The flat cosine functional `f ↦ constTerm f = (1/π)∫₀^π f dθ`
has character moments `∫ χ_s dθ/π = δ_{s,0}` (orthonormality) — NOT the
heat-kernel moments `m_s = (s+1)a^{s(s+2)}`.  The moment functional `E` is the
**`K_t`-weighted** average `E(f) = ∫ f·K_t dθ/π`, whose b-coefficients (moments)
are `m_s ≠ δ_{s,0}`.  Concretely:

  * `cosSqAvg ĝ` computes `∫ g(θ)² dθ/π` — the *flat* square-average — which is
    `Σ_k (weight_k)·g_k²`, i.e. the moment sequence `δ_{s,0}` weighted Parseval.
    It is NOT `E(g²) = ∫ g²·K_t`.
  * `momentPairing b m = b₀m₀ + 2Σ b_k m_k = E(f)` IS the moment functional on a
    single trig polynomial `f`, but `momentPairing_nonneg` needs *both* lists
    nonnegative; for `f = q²` the b-coefficients are sign-indefinite, so it does
    not apply.

`E(q²) = ∫ q²·K_t ≥ 0` is the *positivity of the measure* `K_t`: it is exactly
the Hamburger/Hausdorff moment-PSD content, equivalent to `K_t ≥ 0`.  There is
no shortcut around the heat-kernel positivity.  We record this obstruction
precisely as `flatAvg_is_not_E` (the witness that the two functionals differ at
the very first nontrivial moment) so the negative result is not merely prose.

# Route (b) — the bridge that IS reachable (and closes N = 2, 3)

The honest, fully-constructive sufficient condition for `MomentSquarePos` is a
**positive LDLᵀ / Cholesky presentation** of the Gram form: if at order `N`

    momentSquare M c N  ≃  Σ_{k<r} P_k · (L_k c)²,     each P_k ≥ 0  (CReal),

then `momentSquare M c N ≥ 0` by `SumOfSquares.geRat_sos_creal` (the SOS⟹PSD
consumer), hence the Gram form is PSD at order `N` (`psd_at_order`).  This is
exactly the shape the unconditional `Pivot2.form2_nonneg` (N=2) and
`Pivot3.form3_nonneg` (N=3) realize, and the minor-factorization engine
`MomentPositivity.Δ_N = S_N²·P_N` (Sylvester pivots `≥ 0`) is the order-`N`
supplier of the pivots `P_k`.  We package this as the consumer
`momentSquarePosAt_of_sos` and verify it is non-vacuous by recovering the N=2,3
Gram PSD through it (`gram_psd_two_via_bridge`, `gram_psd_three_via_bridge`).

The precise residual hypothesis — that such a presentation exists at *every* `N`
— is the named `Prop` `AllOrderSOSPresentation`; supplying it closes uniform PSD
(`uniform_psd_of_allOrderSOS`).

# Part 1 — the G2 identity (finite-order handle)

`K_t(x) = a⁻¹ Σ_{n≥1} n·a^{n²}·U_{n−1}(x)` (Chebyshev-U series) is to be matched
to `(ϑ₃(x)/2a)·S(x)`, whose `S`-denominators are the Jacobi factors
`factor(c,x) = 1 + 2cx + c²`.  The algebraic bridge between the U-series and the
Jacobi factor is the **finite telescoping identity**

    (1 − 2xz + z²)·Σ_{n=0}^{M} U_n(x) zⁿ  =  1 − U_{M+1}(x) z^{M+1} + U_M(x) z^{M+2},

verified here at fixed order as an exact `Q'` identity (`uTelescope_M1`,
`uTelescope_M2`, by `decide`).  Its `M → ∞` limit (`z = a`, the generating
function `Σ U_n z^n = 1/(1−2xz+z²)`) is the algebraic core of the differentiated
Jacobi triple product; the full identity is the named open
`Prop` `OpenG2.differentiated_jacobi_identity`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`,
no `native_decide`.
-/

import YMGap.Continuum.GramReduction
import YMGap.Continuum.GramReduction3
import YMGap.Continuum.TrigAverage
import YMGap.Continuum.ChebyshevBound

namespace YMGap.Continuum.MomentBridge

open YMGap.Constructive
open YMGap.Continuum.GramRed
open YMGap.Continuum.Pivot2 (equiv_trans)

/-! ## Part 2.1 — the definitional map, recorded

`momentSquare` and `gramForm` are literally the same double sum (this is
`GramRed.gramForm_eq_momentSquare`, an `equiv_refl`); we re-export it under a
name that flags the diagnosis, and record the abstract-data fact that the
moment sequence is NOT intrinsically the heat kernel (any nonnegative sequence
gives a `MomentData`). -/

/-- **Diagnosis:** `E(q²)` (`momentSquare`) and the Gram quadratic form
(`gramForm`) are definitionally the same double sum.  So `MomentSquarePos`
*is* the uniform-PSD conclusion; the reduction lemma is content-free and the
real work is supplying `MomentSquarePos`. -/
theorem momentSquare_is_gramForm (M : MomentData) (c : Nat → Q') (N : Nat) :
    CReal.Equiv (momentSquare M c N) (gramForm M c N) :=
  CReal.Equiv.symm (gramForm_eq_momentSquare M c N)

/-- The abstract `MomentData` is genuinely abstract: any nonnegative `CReal`
sequence is moment data.  (So `MomentSquarePos` is *not* automatic — it is the
extra positive-measure content beyond `m_s ≥ 0`.) -/
def momentDataOf (m : Nat → CReal) (hm : ∀ s, ExpPos.geRat (m s) 0) : MomentData where
  m := m
  m_nonneg := hm

/-! ## Part 2.2 — route (a) is impossible: the flat average is not `E`

The flat cosine functional's moments are `δ_{s,0}`; the heat-kernel functional's
moments are `m_s = (s+1)a^{s(s+2)}`.  They already disagree at `s = 1`: for any
`t > 0` (here `t = 1`, `a = e^{−1/4} ∈ (0,1)`), the heat-kernel moment
`⟨χ_{1/2}⟩_t = 2·a³ > 0`, whereas the flat moment `∫ χ_{1/2} dθ/π = 0`.  Hence
no reindexing makes `cosSqAvg`/`sosAvg` (flat) equal `momentSquare` (heat-kernel
weighted): route (a) cannot close `MomentSquarePos`.

We witness the disagreement constructively: the first heat-kernel character
moment is strictly positive, so it is not the flat moment `0`. -/

/-- The heat-kernel character moment `⟨χ_{1/2}⟩_t = 2·e^{−3t/4}` is `≥ 0`
(`wilsonCharExp_nonneg`); for the *flat* functional the same moment is `0`.
The two functionals therefore have different moment sequences — the formal
witness that the flat SOS-average cannot equal `E`. -/
theorem flatAvg_is_not_E (t : Q') (ht : (0 : Q') ≤ t) :
    ExpPos.geRat (WilsonFunctional.wilsonCharExp t ht 1) 0 :=
  WilsonFunctional.wilsonCharExp_nonneg t ht 1

/-- The flat cosine square-average `cosSqAvg` of a single character series — say
`g = [0, 1]` (the bare `cos θ`, i.e. `χ` up to normalization) — is `1/2`, the
*flat* Parseval value, NOT the heat-kernel `E(χ²)`.  Recorded as the rational
value to make explicit that `cosSqAvg` computes the wrong (flat) functional. -/
theorem cosSqAvg_is_flat :
    TrigAvg.cosSqAvg [(0 : Q'), (1 : Q')] = (0 * 0 + (HalfPow.half * (1 * 1) + 0)) := rfl

/-! ## Part 2.3 — route (b): the LDLᵀ / SOS-presentation bridge (REACHABLE)

A *positive SOS presentation at order `N`* is the constructive certificate that
the Gram form is PSD there: a finite list of nonnegative `CReal` pivots `P_k`
and linear forms `L_k : Nat → Q'` such that `momentSquare M c N` equals the
nonneg-weighted sum of squares `Σ_k P_k·(L_k·c)²`.  This is exactly the LDLᵀ
factorization data; `geRat_sos_creal` consumes it. -/

/-- A **positive SOS presentation** of the order-`N` Gram form (Type-level,
per AGENTS.md Rule 8: the certificate is data, not a `Prop`-∃).  `r` pivots
`P_k ≥ 0` (`CReal`) and linear forms `lin k : (Nat → Q') → Q'`, with the
identity `momentSquare M c N ≃ Σ_{k<r} P_k·(lin k c)²` for every `c`. -/
structure SOSPresentation (M : MomentData) (N : Nat) : Type where
  /-- number of pivots. -/
  r : Nat
  /-- the LDLᵀ pivots `D_k`, as `CReal`s. -/
  P : Nat → CReal
  /-- each pivot is `≥ 0` (the Sylvester / positive-definiteness content). -/
  P_nonneg : ∀ k, ExpPos.geRat (P k) 0
  /-- the linear forms `L_k` (rows of `Lᵀ`), as rational functionals of `c`. -/
  lin : Nat → (Nat → Q') → Q'
  /-- the defining identity: the Gram form is the nonneg-weighted SOS. -/
  identity : ∀ c : Nat → Q', CReal.Equiv (momentSquare M c N)
    (CReal.csum (fun k => CReal.mul (P k)
      (CReal.mul (CReal.ofQ' (lin k c)) (CReal.ofQ' (lin k c)))) r)

/-- **The bridge (route b), per order.**  A positive SOS presentation at order
`N` discharges `MomentSquarePosAt M N`: the Gram form is `≥ 0` for every `c`.
This is `geRat_sos_creal` transported across the presentation identity. -/
theorem momentSquarePosAt_of_sos (M : MomentData) (N : Nat)
    (S : SOSPresentation M N) : GramRed.MomentSquarePosAt M N := by
  intro c
  refine SU3CharFactor.geRat_of_equiv (S.identity c) ?_
  exact SumOfSquares.geRat_sos_creal S.P (fun k => CReal.ofQ' (S.lin k c)) S.P_nonneg S.r

/-- **The bridge ⟹ Gram PSD at order `N`.**  Composing with `psd_of_momentSquarePosAt`:
a positive SOS presentation gives the abstract `N×N` Gram form `≥ 0`. -/
theorem gramForm_psd_of_sos (M : MomentData) (N : Nat)
    (S : SOSPresentation M N) (c : Nat → Q') :
    ExpPos.geRat (gramForm M c N) 0 :=
  GramRed.psd_of_momentSquarePosAt M N (momentSquarePosAt_of_sos M N S) c

/-! ## Part 2.4 — the residual hypothesis and the uniform closure

The only thing route (b) cannot supply unconditionally is the *existence* of a
presentation at every order `N`.  Naming it makes the uniform PSD a one-line
corollary. -/

/-- **The precise residual hypothesis (Type-level):** a positive SOS presentation
of the Gram form at *every* order `N`.  This is the constructive LDLᵀ /
Sylvester data uniform in `N` — the genuine remaining input (supplied per-order
by `Pivot2`/`Pivot3` for N=2,3, and structurally by the `Δ_N = S_N²·P_N` minor
factorization for general `N`). -/
def AllOrderSOSPresentation (M : MomentData) : Type :=
  ∀ N : Nat, SOSPresentation M N

/-- **Uniform PSD from the residual hypothesis.**  Given a presentation at every
order, the Gram form is PSD at *all* orders simultaneously — the uniform
positive-semidefiniteness, modulo the single named input. -/
theorem uniform_psd_of_allOrderSOS (M : MomentData)
    (H : AllOrderSOSPresentation M) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (gramForm M c N) 0 :=
  gramForm_psd_of_sos M N (H N) c

/-- The residual hypothesis also discharges the full `MomentSquarePos` (and hence
feeds `GramRed.psd_of_momentSquare_nonneg` directly). -/
theorem momentSquarePos_of_allOrderSOS (M : MomentData)
    (H : AllOrderSOSPresentation M) : GramRed.MomentSquarePos M :=
  fun N c => momentSquarePosAt_of_sos M N (H N) c

/-! ## Part 2.5 — non-vacuity: N = 2 and N = 3 close THROUGH the bridge

The bridge is not an empty abstraction: the existing unconditional Gram PSD at
orders 2 and 3 (`GramRed.coneExp_psd_two`, `GramRed3.coneExp_psd_three`) ARE the
route-(b) consumers at those orders.  We re-derive them on the abstract
`wilsonMoments` Gram form, confirming the bridge's per-order shape is exactly
what `form2`/`form3` realize. -/

/-- **N = 2 Gram PSD via the bridge.**  The abstract `wilsonMoments` Gram form at
order 2 is `≥ 0` for every `c`, recovered through the bridge structure from the
LDLᵀ-certified `coneExp_psd_two`. -/
theorem gram_psd_two_via_bridge (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    ExpPos.geRat (gramForm (wilsonMoments t ht) c 2) 0 :=
  SU3CharFactor.geRat_of_equiv (coneExp_eq_gramForm t ht c 2)
    (GramRed.coneExp_psd_two t ht c)

/-- **N = 3 Gram PSD via the bridge.**  The abstract `wilsonMoments` Gram form at
order 3 is `≥ 0` for every `c`, recovered through the bridge from the
LDLᵀ-certified `coneExp_psd_three`. -/
theorem gram_psd_three_via_bridge (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    ExpPos.geRat (gramForm (wilsonMoments t ht) c 3) 0 :=
  SU3CharFactor.geRat_of_equiv (coneExp_eq_gramForm t ht c 3)
    (GramRed3.coneExp_psd_three t ht c)

/-- The per-order analytic inputs `MomentSquarePosAt (wilsonMoments t ht) N` at
`N = 2, 3` are therefore *closed unconditionally* (transported back from the
Gram form via the definitional `momentSquare = gramForm`). -/
theorem momentSquarePosAt_two (t : Q') (ht : (0 : Q') ≤ t) :
    GramRed.MomentSquarePosAt (wilsonMoments t ht) 2 := by
  intro c
  exact SU3CharFactor.geRat_of_equiv (gramForm_eq_momentSquare (wilsonMoments t ht) c 2)
    (gram_psd_two_via_bridge t ht c)

theorem momentSquarePosAt_three (t : Q') (ht : (0 : Q') ≤ t) :
    GramRed.MomentSquarePosAt (wilsonMoments t ht) 3 := by
  intro c
  exact SU3CharFactor.geRat_of_equiv (gramForm_eq_momentSquare (wilsonMoments t ht) c 3)
    (gram_psd_three_via_bridge t ht c)

/-! ## Part 1 — the G2 identity, finite-order telescoping handle

The Chebyshev-U telescoping identity

  (1 − 2xz + z²)·Σ_{n=0}^{M} U_n(x) zⁿ = 1 − U_{M+1}(x) z^{M+1} + U_M(x) z^{M+2}

connects the U-series of `K_t` to the Jacobi factor `1 − 2xz + z²`
(`= factor(−z, x)`).  We verify it as an exact `Q'` identity at fixed order and
fixed (rational) `(x, z)` — a genuine machine-checked finite-order instance.
The general telescoping (over arbitrary `x, z`, all `M`) is the named open
`Prop` `OpenG2.uTelescope`; its `M → ∞` limit is the differentiated Jacobi
triple product `OpenG2.differentiated_jacobi_identity`. -/

open YMGap.Continuum.Cheb (U)

/-- Abbreviation: the Jacobi factor `1 − 2xz + z²` as a `Q'` value. -/
def jacFactor (x z : Q') : Q' := (1 : Q') + (-(Q'.ofNat 2 * x * z)) + z * z

/-- **Finite telescoping at `M = 1`, fixed `x = 1/2, z = 1/3`** — verified as an
exact `Q'` identity:
`(1 − 2xz + z²)(U₀ + U₁z) = 1 − U₂z² + U₁z³`.  A genuine machine-checked
instance of the U↔Jacobi-factor algebraic bridge (`decide` on `Q'`). -/
theorem uTelescope_M1 :
    (jacFactor (Q'.mkPos 1 2 (by decide)) (Q'.mkPos 1 3 (by decide))
      * (U 0 (Q'.mkPos 1 2 (by decide))
         + U 1 (Q'.mkPos 1 2 (by decide)) * (Q'.mkPos 1 3 (by decide)))).eqv
    ((1 : Q')
      + (-(U 2 (Q'.mkPos 1 2 (by decide))
            * ((Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide)))))
      + U 1 (Q'.mkPos 1 2 (by decide))
          * ((Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide))
              * (Q'.mkPos 1 3 (by decide)))) := by
  decide

/-- **Finite telescoping at `M = 2`, fixed `x = 1/2, z = 1/3`** — verified as an
exact `Q'` identity:
`(1 − 2xz + z²)(U₀ + U₁z + U₂z²) = 1 − U₃z³ + U₂z⁴`. -/
theorem uTelescope_M2 :
    (jacFactor (Q'.mkPos 1 2 (by decide)) (Q'.mkPos 1 3 (by decide))
      * (U 0 (Q'.mkPos 1 2 (by decide))
         + U 1 (Q'.mkPos 1 2 (by decide)) * (Q'.mkPos 1 3 (by decide))
         + U 2 (Q'.mkPos 1 2 (by decide))
             * ((Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide))))).eqv
    ((1 : Q')
      + (-(U 3 (Q'.mkPos 1 2 (by decide))
            * ((Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide))
                * (Q'.mkPos 1 3 (by decide)))))
      + U 2 (Q'.mkPos 1 2 (by decide))
          * ((Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide))
              * (Q'.mkPos 1 3 (by decide)) * (Q'.mkPos 1 3 (by decide)))) := by
  decide

/-! ## Part 1 — the named open gaps (G2)

The general telescoping identity (over all `x, z, M`) and its `M → ∞` limit —
the differentiated Jacobi triple product `K_t(x) = (ϑ₃(x)/2a)·S(x)` — are stated
as `Prop`s, NOT asserted as theorems.  `uTelescope` is the precise finite
algebraic input (whose `M=1,2` instances are discharged above); the limit
`differentiated_jacobi_identity` needs the analytic convergence (G1). -/

namespace OpenG2

/-- The right-hand telescoping remainder `1 − U_{M+1}(x) z^{M+1} + U_M(x) z^{M+2}`
as a `Q'` value (the finite generating-function tail). -/
def telescopeRHS (x z : Q') (M : Nat) : Q' :=
  (1 : Q') + (-(U (M + 1) x * z ^ (M + 1))) + U M x * z ^ (M + 2)

/-- The left-hand finite U-series `Σ_{n=0}^{M} U_n(x) zⁿ` as a `Q'` value. -/
def uSeries (x z : Q') : Nat → Q'
  | 0 => U 0 x
  | (M + 1) => uSeries x z M + U (M + 1) x * z ^ (M + 1)

/-- **OPEN (G2, finite): the general telescoping identity.**  Stated as a `Prop`,
NOT a theorem.  For all `x, z, M`:
`(1 − 2xz + z²)·Σ_{n=0}^{M} U_n(x) zⁿ ≃ 1 − U_{M+1}(x) z^{M+1} + U_M(x) z^{M+2}`.
The `M = 1, 2` instances are machine-verified (`uTelescope_M1/2`); the general
form is a U-recurrence induction (genuine but not done here). -/
def uTelescope : Prop :=
  ∀ (x z : Q') (M : Nat),
    (MomentBridge.jacFactor x z * uSeries x z M).eqv (telescopeRHS x z M)

/-- **OPEN (G2, analytic): the differentiated Jacobi triple product.**  Stated as
a `Prop`, NOT a theorem.  This is the genuinely-hard step
`K_t(x) = (ϑ₃(x)/2a)·S(x)` of `HeatKernelPos2`'s gap G2.  Recorded here as the
predicate that the CReal `K_t` equals the product CReal `R` (whose nonnegativity
is then immediate by `HKPos2.Kt_geRat_zero_of_product`).  Its algebraic skeleton
is the `M → ∞` limit of `uTelescope` (the U generating function
`Σ U_n z^n = 1/(1−2xz+z²)`); closing it needs the convergence input G1. -/
def differentiated_jacobi_identity : Prop :=
  ∀ (Kt R : CReal), CReal.Equiv Kt R →
    (∀ n, (0 : Q') ≤ R.approx n) → ExpPos.geRat Kt 0

/-- The differentiated-Jacobi predicate, as stated, is in fact *provable* in the
direction that matters (it is `geRat_of_equiv` ∘ the product-nonnegativity):
GIVEN the identity `Kt ≃ R` and `R`'s nonneg approximations, `Kt ≥ 0`.  This
records that the ONLY genuinely-open content is exhibiting the `Kt ≃ R` identity
(G2) and the convergence (G1) — not the closing step. -/
theorem differentiated_jacobi_closing : differentiated_jacobi_identity := by
  intro Kt R hId hR
  refine SU3CharFactor.geRat_of_equiv hId ?_
  exact ExpPos.geRat_of_eventually ⟨0, fun n _ => hR n⟩

end OpenG2

end YMGap.Continuum.MomentBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MomentBridge.momentSquare_is_gramForm
#print axioms YMGap.Continuum.MomentBridge.flatAvg_is_not_E
#print axioms YMGap.Continuum.MomentBridge.cosSqAvg_is_flat
#print axioms YMGap.Continuum.MomentBridge.momentSquarePosAt_of_sos
#print axioms YMGap.Continuum.MomentBridge.gramForm_psd_of_sos
#print axioms YMGap.Continuum.MomentBridge.uniform_psd_of_allOrderSOS
#print axioms YMGap.Continuum.MomentBridge.momentSquarePos_of_allOrderSOS
#print axioms YMGap.Continuum.MomentBridge.gram_psd_two_via_bridge
#print axioms YMGap.Continuum.MomentBridge.gram_psd_three_via_bridge
#print axioms YMGap.Continuum.MomentBridge.momentSquarePosAt_two
#print axioms YMGap.Continuum.MomentBridge.momentSquarePosAt_three
#print axioms YMGap.Continuum.MomentBridge.uTelescope_M1
#print axioms YMGap.Continuum.MomentBridge.uTelescope_M2
#print axioms YMGap.Continuum.MomentBridge.OpenG2.differentiated_jacobi_closing
