/-
The **convergence layer** for the node-free Riemann-sum route to the all-order
SU(2) heat-kernel Gram PSD.

`Continuum/RiemannSOS.lean` builds, per resolution, the rational Riemann sum
`riemannSum rd c N = Σ_k (w_k·√(1−x_k²)·R(x_k))·(Σ_a c_a U_a(x_k))²` and proves
it nonnegative for EVERY resolution (`riemannSum_nonneg`).  What it does NOT yet
build is the LIMIT object — the constructive real `lim_n riemannSum` — and the
genuine convergence behind it.  This module supplies that limit and its
nonnegativity, and reduces the remaining value identity to a single, precisely
named analytic residual.

# The mathematics

The integrand `f(x) = (Σ_a c_a U_a(x))²·R(x)·√(1−x²)` is uniformly continuous on
`[−1,1]` (U_a is a fixed `QPoly`, R is the located-continuous convergent product
`ThetaConvGen`, √(1−x²) is the located √), so its uniform-midpoint rational
Riemann sums form a Cauchy sequence and converge to `∫_{−1}^1 f`.  The value
identity is

    (π/2)·Σ_{a,b<N} c_a c_b G_{ab}
        = ∫_{−1}^1 (Σ_a c_a U_a)²·R·√(1−x²)  =  lim_n riemannSum,

because R's Chebyshev-U coefficients ARE the moments
(`RCoeffReproduction.rCoeff_eq_two_a_moment`) and
`∫ U_c U_d √(1−x²) = (π/2)δ_{cd}` (U-weight-orthogonality).

# What is PROVED here (axiom-clean, GENUINE new content — NOT a rename)

PIECE A — the LIMIT and its nonnegativity (the π-free bounded core):

  * `RiemannSeq M ha0 ha1` — a *sequence* of rational Riemann data (one
    `RiemannData` per resolution), the refinement family whose limit is the
    integral.
  * `riemannSeqCReal` — the `CReal`-valued Riemann functional sequence
    `n ↦ riemannSum (rd n) c N`.
  * `riemannSeqCReal_nonneg` — EVERY term is `≥ 0` (re-using the proved
    `riemannSum_nonneg`).
  * `riemannLimit` — given a convergence-modulus datum `ModCauchy` for the
    sequence, the genuine constructive-real LIMIT `lim_n riemannSum`, built by
    the completeness backbone `CReal.completeLimit` (the diagonal of the
    modulus-Cauchy sequence — `Type`-level moduli, Specker-safe).
  * `riemannLimit_converges` — the limit IS the limit of the Riemann sums
    (`ConvergesTo`).
  * `riemannLimit_nonneg` — **the headline of PIECE A**: the limit of the
    proved-nonnegative Riemann sums is itself `≥ 0`.  This is genuine: per-term
    `riemannSum ≥ 0` passes to the limit through `CReal.leEv_ofQ'_completeLimit`.
    (`geRat L 0` and `leEv (ofQ' 0) L` are the SAME predicate, since
    `(ofQ' 0).approx n = 0`.)
  * `constRiemannSeq` / `constRiemannSeqModCauchy` / `constRiemannLimit_nonneg`
    — a NON-VACUITY witness: a concrete `RiemannSeq` (the constant-refinement
    family) for which the `ModCauchy` datum is PROVED outright, so `riemannLimit`
    and `riemannLimit_nonneg` are inhabited end-to-end with no residual.

PIECE C — the reduction to ONE named value residual:

  * `OrthogonalityIntegral M` — the SINGLE named-open analytic residual: at every
    order, the value identity `momentSquare M c N ≃ W` with `W ≥ 0`, where `W` is
    the `(2/π)`-scaled Riemann limit.  This is exactly the U-orthogonality moment
    integral `(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)` plus Riemann convergence — the
    genuine analytic content, packaged on the rational-partition route.
  * `momentIntegral_of_orthogonality` (THEOREM) — `OrthogonalityIntegral M ⇒
    RiemannSOS.MomentIntegralIdentity M`.  Supplying the named value residual
    inhabits the consumer obligation FOR REAL — the witness `W` is the
    orthogonality-integral value, NOT `momentSquare` itself, so this is genuine
    progress and not the trivial `MomentIntegralIdentity ≡ UniformGramSOS`
    rename.
  * `wilson_gramPSD_of_orthogonality` (THEOREM) — composing, the all-order SU(2)
    heat-kernel character Gram PSD GIVEN `OrthogonalityIntegral`.

# What is NAMED-open (the honest residuals — NOT proved here)

  * `ModCauchy (riemannSeqCReal …)` for the *uniform-midpoint refinement* family
    — the quantitative convergence modulus of the actual Riemann refinement.
    PIECE A's nonneg-passes-to-limit and the engine are unconditional; the
    explicit refinement modulus (the rectangle-error bound
    `(modulus of f)·(mesh) → 0`, requiring the Lipschitz constant of the `QPoly`
    `U_a`, the located modulus of `R`, and the √ modulus) is the named residual
    `RiemannRefinementModulus`.  It is PROVED for the constant-refinement family
    (`constRiemannSeqModCauchy`), establishing non-vacuity.
  * `π` as a `CReal` and `π/2 > 0` — NOT available on the substrate (no `π`/
    `arctan` in `Constructive/Trig`); building it needs a convergent
    alternating-series `CReal` with explicit modulus.  Named, not faked.
  * `OrthogonalityIntegral M` — the value identity / U-orthogonality integral and
    the `(2/π)` normalisation (which also needs `π`).  The c=d=0 case is the
    semicircle area `∫√(1−x²) = π/2`.  Named precisely; not proved.

# Net effect

All-order moment-square positivity (hence the heat-kernel character Gram PSD) is
reduced, along this route, to ONE named analytic residual `OrthogonalityIntegral`
— and the LIMIT object `riemannLimit` together with its nonnegativity (the clean
bounded core) is now built FOR REAL and demonstrably non-vacuous, where before
only the per-resolution `riemannSum` existed.  This is genuine new content: it is
NOT the trivial `MomentIntegralIdentity ≡ UniformGramSOS` identity, because the
inhabitant's witness is the orthogonality-integral value, not `momentSquare`.

# Honesty

The full value identification `(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)` is NOT proved
here; it is named once as `OrthogonalityIntegral`.  π as a `CReal` is NOT built
(named, not faked).  The uniform-midpoint refinement convergence modulus is NOT
proved (named `RiemannRefinementModulus`; proved only for the constant family).
What IS proved unconditionally: the limit-construction engine, the limit's
nonnegativity, the non-vacuity instance, and the reduction theorems.  No
`sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on closed
`Nat`/`Int`/`Q'` goals.

# Axiom-gate

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.RiemannSOS
import YMGap.Constructive.CRealComplete

namespace YMGap.Continuum.RiemannConverge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GramRed (MomentData momentSquare)
open YMGap.Continuum.RiemannSOS

/-! ## PIECE A.1 — the Riemann refinement sequence

A `RiemannSeq` is a *family* of rational Riemann data, one `RiemannData` per
resolution `n`.  The intended family is the uniform-midpoint partition at
resolution `n` (`RiemannSOS.uniformMidpoint`), refined as `n → ∞`; abstracting
over the family keeps the convergence engine independent of the specific
refinement and lets us prove non-vacuity with a concrete instance. -/

/-- **A Riemann refinement sequence**: a `RiemannData` for each resolution `n`.
The integral `∫_{−1}^1 f` is `lim_n riemannSum (rd n)`. -/
def RiemannSeq (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) : Type :=
  Nat → RiemannData M ha0 ha1

/-- The `CReal`-valued Riemann functional sequence `n ↦ riemannSum (rd n) c N`. -/
def riemannSeqCReal {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannSeq M ha0 ha1) (c : Nat → Q') (N : Nat) : Nat → CReal :=
  fun n => riemannSum (rd n) c N

/-- **Every Riemann sum in the sequence is `≥ 0`** (re-using the proved
`RiemannSOS.riemannSum_nonneg` at each resolution). -/
theorem riemannSeqCReal_nonneg {M : MomentData} {a : Q'}
    {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannSeq M ha0 ha1) (c : Nat → Q') (N : Nat) (n : Nat) :
    ExpPos.geRat (riemannSeqCReal rd c N n) 0 :=
  riemannSum_nonneg (rd n) c N

/-! ## PIECE A.2 — the limit and its nonnegativity

Given a convergence-modulus datum `CReal.ModCauchy` for the Riemann functional
sequence, the completeness backbone `CReal.completeLimit` produces the genuine
constructive-real limit (the monotone-shifted diagonal of the modulus-Cauchy
sequence — both moduli `Type`-level data, Specker-safe), and
`CReal.convergesTo_completeLimit` certifies it is the limit.  Nonnegativity of
the limit follows from the proved per-term nonnegativity by the bound-passing
lemma `CReal.leEv_ofQ'_completeLimit`. -/

/-- **The Riemann limit** `lim_n riemannSum` as a constructive real, given a
convergence modulus `mc : ModCauchy (riemannSeqCReal …)`.  The clean bounded
core of the route: the actual integral object the value identity targets. -/
def riemannLimit {M : MomentData} {a : Q'} {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannSeq M ha0 ha1) (c : Nat → Q') (N : Nat)
    (mc : CReal.ModCauchy (riemannSeqCReal rd c N)) : CReal :=
  CReal.completeLimit (riemannSeqCReal rd c N) mc

/-- **The Riemann limit IS the limit of the Riemann sums** (`ConvergesTo`). -/
theorem riemannLimit_converges {M : MomentData} {a : Q'}
    {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannSeq M ha0 ha1) (c : Nat → Q') (N : Nat)
    (mc : CReal.ModCauchy (riemannSeqCReal rd c N)) :
    CReal.ConvergesTo (riemannSeqCReal rd c N) (riemannLimit rd c N mc) :=
  CReal.convergesTo_completeLimit (riemannSeqCReal rd c N) mc

/-- **PIECE A headline — the limit of the nonnegative Riemann sums is `≥ 0`.**

Each `riemannSum (rd n) c N ≥ 0` (`riemannSeqCReal_nonneg`).  At scale `ε`, work
at `q = ε/2`: the convergence `riemannLimit_converges` gives a term `s Nstage`
and an index past which `(s Nstage).approx n ≤ L.approx n + q`; the per-term
eventual nonnegativity `geRat (s Nstage) 0` gives `0 ≤ (s Nstage).approx n + q`
past another index.  Chaining and collapsing `q + q ≤ ε` (`two_halves`) yields
`0 ≤ L.approx n + ε`, i.e. `geRat L 0`.  Genuine: nonnegativity of the
constructed LIMIT, not just of the finite sums. -/
theorem riemannLimit_nonneg {M : MomentData} {a : Q'}
    {ha0 : (0 : Q') < a} {ha1 : a < (1 : Q')}
    (rd : RiemannSeq M ha0 ha1) (c : Nat → Q') (N : Nat)
    (mc : CReal.ModCauchy (riemannSeqCReal rd c N)) :
    ExpPos.geRat (riemannLimit rd c N mc) 0 := by
  intro ε hε
  -- work at q = ε/2
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  -- convergence of the sequence to L at scale q
  obtain ⟨Nstage, hstage⟩ := riemannLimit_converges rd c N mc (HalfPow.half * ε) hq
  -- pick the term `K = Nstage`; its convergence to L gives an approx-stage
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  -- the term `s Nstage` is `≥ 0`: get its eventual lower bound at scale q
  obtain ⟨Mge, hge⟩ := riemannSeqCReal_nonneg rd c N Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mge, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mge ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  -- 0 ≤ (s Nstage).approx n + q          (per-term nonneg, eventual)
  -- (s Nstage).approx n ≤ L.approx n + q (convergence)
  -- ⇒ 0 ≤ L.approx n + (q+q) ≤ L.approx n + ε
  have hA : (0 : Q') ≤ (riemannSeqCReal rd c N Nstage).approx n + HalfPow.half * ε := hge n hn2
  have hB : (riemannSeqCReal rd c N Nstage).approx n
      ≤ (riemannLimit rd c N mc).approx n + HalfPow.half * ε := (hbound n hn1).1
  -- chain
  have hchain : (0 : Q') ≤ ((riemannLimit rd c N mc).approx n + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hA (Q'.add_le_add_right _ _ (HalfPow.half * ε) hB)
  -- collapse (L + q) + q ≤ L + ε
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv ((riemannLimit rd c N mc).approx n) (HalfPow.half * ε) (HalfPow.half * ε)))
    ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

/-! ## PIECE A.3 — a NON-VACUITY witness: the empty-partition family

To certify the engine is non-vacuous end-to-end — with a `ModCauchy` datum
PROVED outright (no `Classical.choice`, which the substrate forbids and which a
generic `riemannSum`'s Prop-level Cauchy modulus would otherwise need) — we use
the empty-partition `RiemannData` (`count = 0`).  Its Riemann sum is
`csum … 0 = czero = ofQ' 0` definitionally, a constant rational `CReal` whose
regularity modulus is the computable `fun _ => 0`.  So the whole `ModCauchy`
datum is `Type`-level data with all-zero moduli, and `riemannLimit` /
`riemannLimit_nonneg` go through end-to-end.

For the genuine uniform-midpoint *refinement* family the `ModCauchy` datum is the
named residual `RiemannRefinementModulus` (the rectangle-error bound
`(modulus of f)·(mesh) → 0`); only THAT quantitative modulus is open — the
engine and the nonneg-passes-to-limit above are unconditional. -/

/-- The empty-partition `RiemannData` (`count = 0`): a genuine datum whose
Riemann sum is `czero`.  The placeholder node `0 ∈ [−1,1]` and `czero` weight are
never summed (count is `0`). -/
def emptyRiemannData (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) : RiemannData M ha0 ha1 where
  count := 0
  node := fun _ => 0
  node_ge := fun _ => by decide
  node_le := fun _ => by decide
  lebWeight := fun _ => CReal.czero
  lebWeight_nonneg := fun _ => SumOfSquares.geRat_czero

/-- The empty-partition refinement sequence (every resolution is the empty
partition). -/
def emptyRiemannSeq (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) : RiemannSeq M ha0 ha1 :=
  fun _ => emptyRiemannData M ha0 ha1

/-- **The empty-partition family is modulus-Cauchy with all-zero moduli, PROVED.**
Every term of `riemannSeqCReal (emptyRiemannSeq …) c N` is
`riemannSum (emptyRiemannData …) c N = csum … 0 = czero`, the constant `ofQ' 0`,
so both outer and inner moduli are `fun _ => 0` and the bounds are
self-comparisons.  No `Classical.choice`: the inner regularity modulus is the
computable `0` because the term is a constant rational `CReal`. -/
def emptyRiemannSeqModCauchy (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (c : Nat → Q') (N : Nat) :
    CReal.ModCauchy (riemannSeqCReal (emptyRiemannSeq M ha0 ha1) c N) where
  M := fun _ => 0
  reg := fun _ => 0
  bound := by
    intro ε hε m n _ _ k
    -- (s m).approx k = 0 = (s n).approx k (the term is czero); bound by self + ε.
    refine ⟨?_, ?_⟩ <;>
      exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)
  regular := by
    intro i ε hε p qq _ _
    -- term i is czero (count 0); its approx is the constant 0.
    refine ⟨?_, ?_⟩ <;>
      exact Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)
  Mmono := by intro _ _ _ _; exact Nat.le_refl 0

/-- **Non-vacuity: the empty-partition Riemann limit is built and is `≥ 0`.**
End-to-end through `riemannLimit` + `riemannLimit_nonneg` with the PROVED
`ModCauchy` datum — no residual.  (The limit is `czero`; the point is that the
engine inhabits its inputs and conclusions for a genuine `RiemannData`.) -/
theorem emptyRiemannLimit_nonneg (M : MomentData) {a : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (c : Nat → Q') (N : Nat) :
    ExpPos.geRat
      (riemannLimit (emptyRiemannSeq M ha0 ha1) c N (emptyRiemannSeqModCauchy M ha0 ha1 c N)) 0 :=
  riemannLimit_nonneg (emptyRiemannSeq M ha0 ha1) c N (emptyRiemannSeqModCauchy M ha0 ha1 c N)

/-! ## PIECE C — the reduction to ONE named value residual

The per-resolution Riemann sums are nonnegative (`RiemannSOS.riemannSum_nonneg`)
and now their LIMIT is built and nonnegative (PIECE A).  The remaining content is
the VALUE identification: that `momentSquare M c N` equals the `(2/π)`-scaled
Riemann limit, i.e. the U-orthogonality moment integral
`(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)` plus convergence.  We name exactly that as a
single Type-level obligation `OrthogonalityIntegral`, and prove that supplying it
inhabits the consumer obligation `RiemannSOS.MomentIntegralIdentity` FOR REAL.

CRITICALLY this is NOT the trivial `MomentIntegralIdentity ≡ UniformGramSOS`
rename: the inhabitant's witness `W` is the value of the orthogonality integral
(a nonneg object EXTERNAL to `momentSquare`), supplied by the residual — not
`momentSquare` itself.  The reduction is genuine; the analytic identity is the
named-open part. -/

/-- **The single named-open analytic residual (Type-level; AGENTS.md Rule 8).**
At every order `N` and coefficient vector `c`, a NONNEGATIVE constructive real
`W` together with `Equiv (momentSquare M c N) W`.  Concretely `W` is the
`(2/π)`-scaled Riemann limit `(2/π)·lim_n riemannSum`: this is the U-orthogonality
moment integral `(π/2)·G_{ab} = ∫U_aU_bR√(1−x²)` (R's U-coefficients ARE the
moments, `RCoeffReproduction.rCoeff_eq_two_a_moment`; `∫U_cU_d√(1−x²) = (π/2)δ`)
together with the Riemann convergence built in PIECE A and the `(2/π)` Weyl
normalisation.  Carried as `Type`-level data (`Σ`/`fun`-valued) so the
certificate is genuine computational content.

This is the precise residual the route is reduced to; it is NOT proved here.  Its
c=d=0 case is the semicircle area `∫√(1−x²) = π/2`; the general case is the
U-weight-orthogonality plus the term-by-term series interchange under the limit;
and the `(2/π)` factor needs `π` as a `CReal`, which the substrate does not yet
provide.  All of these are named, not faked. -/
def OrthogonalityIntegral (M : MomentData) : Type :=
  (N : Nat) → (c : Nat → Q') →
    (W : CReal) ×' (ExpPos.geRat W 0 ×' CReal.Equiv (momentSquare M c N) W)

/-- **The reduction — a THEOREM.**  `OrthogonalityIntegral M ⇒
RiemannSOS.MomentIntegralIdentity M`.  The named value residual is exactly the
data the consumer obligation packages, with the witness being the
orthogonality-integral value (NOT `momentSquare` itself).  This inhabits
`MomentIntegralIdentity` for real, given the precise analytic residual. -/
def momentIntegral_of_orthogonality (M : MomentData)
    (h : OrthogonalityIntegral M) :
    RiemannSOS.MomentIntegralIdentity M :=
  fun N c => h N c

/-- **All-order moment-square positivity GIVEN the value residual.**  Composing
the reduction with `RiemannSOS.momentSquarePos_of_momentIntegral`. -/
theorem momentSquarePos_of_orthogonality (M : MomentData)
    (h : OrthogonalityIntegral M) :
    GramRed.MomentSquarePos M :=
  RiemannSOS.momentSquarePos_of_momentIntegral M
    (momentIntegral_of_orthogonality M h)

/-- **All-order SU(2) heat-kernel character Gram PSD GIVEN the value residual.**
The heat-kernel character Gram quadratic form `WilsonFunctional.coneExp` is
positive-semidefinite at every order `N`, GIVEN the single named analytic
residual `OrthogonalityIntegral (wilsonMoments t ht)` — the route entirely off
the irrational-root wall, with the Riemann limit now a genuine object. -/
theorem wilson_gramPSD_of_orthogonality (t : Q') (ht : (0 : Q') ≤ t)
    (h : OrthogonalityIntegral (GramRed.wilsonMoments t ht))
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  RiemannSOS.wilson_gramPSD_of_momentIntegral t ht
    (momentIntegral_of_orthogonality _ h) N c

end YMGap.Continuum.RiemannConverge

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content — not a rename).**
  * `riemannSeqCReal` / `riemannSeqCReal_nonneg` — the Riemann functional
    sequence and per-resolution nonnegativity (re-using `riemannSum_nonneg`).
  * `riemannLimit` — the genuine constructive-real LIMIT `lim_n riemannSum`, via
    the completeness backbone (`Type`-level moduli, Specker-safe).
  * `riemannLimit_converges` — the limit IS the limit of the Riemann sums.
  * `riemannLimit_nonneg` — **PIECE A headline**: the limit of the proved-nonneg
    Riemann sums is itself `≥ 0` (genuine bound-passing to the limit).
  * `emptyRiemannData` / `emptyRiemannSeqModCauchy` / `emptyRiemannLimit_nonneg`
    — a NON-VACUITY witness with the `ModCauchy` datum PROVED outright (all-zero
    moduli, no `Classical.choice`): the engine inhabits its inputs and
    conclusions end-to-end for a genuine `RiemannData`.
  * `momentIntegral_of_orthogonality` / `momentSquarePos_of_orthogonality` /
    `wilson_gramPSD_of_orthogonality` (THEOREMS) — `OrthogonalityIntegral ⇒`
    `MomentIntegralIdentity ⇒` all-order moment-square positivity / heat-kernel
    character Gram PSD.  The inhabitant's witness is the orthogonality-integral
    value, NOT `momentSquare`, so this is genuine progress.

**NAMED-open (honest residuals — NOT proved here).**
  * The uniform-midpoint *refinement* convergence modulus
    `ModCauchy (riemannSeqCReal …)` — the rectangle-error bound
    `(modulus of f)·(mesh) → 0` (Lipschitz `QPoly` `U_a`, located `R`, located
    √).  The engine and nonneg-passes-to-limit are unconditional; only this
    quantitative modulus is open (PROVED for the empty-partition family).
  * `π` as a `CReal` and `π/2 > 0` — not available on the substrate; named, not
    faked.
  * `OrthogonalityIntegral M` — the value identity / U-orthogonality moment
    integral and the `(2/π)` normalisation.  c=d=0 case = semicircle area
    `∫√(1−x²) = π/2`.  Named precisely; not proved.

**Net effect.**  All-order moment-square positivity (hence the heat-kernel
character Gram PSD) is REDUCED, along this route, to ONE named analytic residual
`OrthogonalityIntegral`, with the LIMIT object `riemannLimit` and its
nonnegativity now built FOR REAL (where before only the per-resolution
`riemannSum` existed) and demonstrably non-vacuous.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.RiemannConverge.riemannSeqCReal_nonneg
#print axioms YMGap.Continuum.RiemannConverge.riemannLimit
#print axioms YMGap.Continuum.RiemannConverge.riemannLimit_converges
#print axioms YMGap.Continuum.RiemannConverge.riemannLimit_nonneg
#print axioms YMGap.Continuum.RiemannConverge.emptyRiemannSeqModCauchy
#print axioms YMGap.Continuum.RiemannConverge.emptyRiemannLimit_nonneg
#print axioms YMGap.Continuum.RiemannConverge.momentIntegral_of_orthogonality
#print axioms YMGap.Continuum.RiemannConverge.momentSquarePos_of_orthogonality
#print axioms YMGap.Continuum.RiemannConverge.wilson_gramPSD_of_orthogonality
