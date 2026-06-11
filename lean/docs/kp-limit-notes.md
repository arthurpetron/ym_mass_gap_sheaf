# KP infinite-volume limit — progress notes (Track B / E2)

This note records one genuine, fully-proved, axiom-clean rung of the
Kotecký–Preiss (KP) thermodynamic / infinite-volume limit, and an honest
accounting of what remains open.  It directly addresses the OPEN item
flagged in `e2-e3-notes.md`:

> KP / cluster infinite-volume convergence WITH a modulus … "the
> reweighted product functionals `E_{β,n}` converge as `n → ∞` with an
> explicit Cauchy modulus" is not assembled.

The module `YMGap/Continuum/KPLimit.lean` assembles the **engine** of that
step: it turns the geometric increment bound that a convergent cluster
expansion produces into a genuine `CReal` infinite-volume limit with an
explicit Cauchy modulus.

## The mathematics

In the convergent (high-β / small-activity) regime, the finite-volume
expectations `⟨o⟩_Λ` form a Cauchy sequence in the volume `Λ`.  KP cluster
convergence gives a **geometric increment bound**

    | ⟨o⟩_{Λ+1} − ⟨o⟩_Λ |  ≤  C · ρ^Λ ,     0 ≤ ρ < 1,

the geometric tail being the residual polymer activity of the polymers
that touch the boundary shell added when the volume grows from `Λ` to
`Λ+1`.  Telescoping, for any gap `d`,

    | ⟨o⟩_{Λ+d} − ⟨o⟩_Λ |  ≤  C·(ρ^Λ + … + ρ^{Λ+d−1})  ≤  (C/(1−ρ))·ρ^Λ ,

which → 0 as `Λ → ∞`.  Hence the sequence is Cauchy with the explicit
modulus inherited from `ρ^Λ → 0`, and `⟨o⟩_∞ = lim_Λ ⟨o⟩_Λ` exists as a
`CReal`.

## What was proved (module `YMGap/Continuum/KPLimit.lean`)

All statements are constructive, Mathlib-free, and axiom-clean
(`[propext]`, plus `Quot.sound` where `Nat`/`omega`/`finSum` recursion
enters).  No `Classical.*`, no `sorryAx`, no `sorry`, no `native_decide`.
Verified by the `#print axioms` block at the bottom of the module.

### Layer 1 — the reusable abstraction

- `crealOfTail (S T : Nat → Q') …` — **the Cauchy-from-tail engine.**
  Given a `Q'` partial-sum sequence `S`, a tail-bound family `T`, the
  two-sided telescoped bounds `S (n+d) ≤ S n + T n` and
  `S n ≤ S (n+d) + T n`, and a modulus `∀ ε>0, ∃ N, ∀ n≥N, T n ≤ ε`,
  it packages `S` as a `CReal` with `approx = S`.  The two-sided
  telescoped tail bound is *exactly* the `CReal.cauchy` field, so the
  Bishop-regular-Cauchy repackaging needs no regularity surgery and no
  rational absolute value / triangle inequality.

### Layer 2 — the geometric (ρ = 1/2) instantiation

- `Q'.pow_add_eqv` — `q^(a+b) ≃ q^a · q^b`.
- `geoIncr C l = C·(1/2)^l`, `geoTail C n = (2C)·(1/2)^n` (definitions),
  with `geoIncr_nonneg`, `geoTail_nonneg`, `geoIncr_shift_eqv`.
- `geom_half_series_le` — the pure geometric series `Σ_{i<d} K·(1/2)^i ≤
  2K`, via the repo's `CharacterTail.geom_series_le` (which in turn uses
  `RationalTail.geometric_tail_closure`) at `f0 = K`, `r = 1/2`,
  `H = 2K`, recurrence `K + (1/2)(2K) = 2K`.
- `geoTail_series_le` — **the telescoped tail bound:**
  `Σ_{i<d} geoIncr C (n+i) ≤ geoTail C n`, combining the `(1/2)^n`
  factorization with the geometric series bound.
- `telescope_up` / `telescope_lo` — the two-sided telescoped bounds from
  single-step increments (induction on the gap `d`, additive
  associativity only).
- `half_pow_le_succ`, `half_pow_add_le`, `half_pow_antitone` —
  antitonicity of `(1/2)^n`.
- `geoTail_modulus` — **the modulus `geoTail C n → 0`,** with explicit
  stage `N = δ.den` from `HalfPow.pow_half_le` (the repo's closed-form
  `(1/2)^k → 0` modulus), given a rescaling witness
  `(2C)·δ ≤ ε` (discharged by `decide` at concrete `C`).

### Capstone

- `crealOfGeoIncrement (S : Nat → Q') (C : Q') …` — **the KP engine:**
  from a two-sided SINGLE-STEP geometric increment bound on `S`
  (`S (Λ+1) ≤ S Λ + C·(1/2)^Λ` and the reverse) plus the rescaling
  modulus, conclude `S` is a `CReal`.  `crealOfGeoIncrement_approx`:
  its `approx Λ = S Λ`, i.e. the limit really is the `Λ → ∞` limit of
  the finite-volume partial sums.

- `geoPolymerSum`, `geoPolymerLimit` — **a concrete convergent polymer
  sum and its limit.**  The geometric activity sum
  `S Λ = Σ_{l<Λ} (1/2)^l` (decay rate `ρ = 1/2 < 1`, the small-activity
  KP regime) has single-step increment exactly the activity `(1/2)^Λ`,
  so the engine applies with `C = 1` and modulus `δ = ε/2`.  The limit
  `geoPolymerLimit` is a genuine `CReal` whose `approx Λ` is the
  finite-volume partial sum (`geoPolymerLimit_approx`), carrying the
  explicit Cauchy modulus.  (Its exact value is `2`; only EXISTENCE with
  modulus is claimed and proved.)

## How it fits / connects to the existing smallness

The repo already closes the **activity smallness** input that KP needs:
`Constructive/SU3CharFactor.lean` proves the SU(3) character-tail bound
`Z_t ≤ (801/800)² − 1 < 1/16` via a geometric domination
(`gBound_dom`, ratio `rTail = 16·(5/12)^{11}`) fed through
`finSum_geom_uniform`.  That is exactly a geometric-increment structure
of the same shape this engine consumes: a nonnegative term sequence with
a `< 1` geometric ratio whose partial sums are uniformly bounded.  The
engine here is the **second half** — converting such smallness into an
infinite-volume limit with modulus — and `crealOfGeoIncrement` /
`geoPolymerLimit` demonstrate the full pipeline end-to-end on the
canonical geometric activity.

## OPEN — what genuinely remains

The engine is proved; the following are NOT done and are the honest
remaining content.

1. **General rational ratio `ρ < 1` → `pow → 0` modulus.**  The engine
   carries `ρ = 1/2` because that is the only decay rate with an explicit
   `pow → 0` modulus already in the repo (`HalfPow.pow_half_le`).  Any
   `ρ ≤ 1/2` is covered by termwise domination, but the actual KP ratio
   (e.g. `16·(5/12)^{11}` from `SU3CharFactor`, which is `< 1/900 < 1/2`,
   so in fact already dominated) deserves a general lemma
   `pow_lt_one_tendsto_zero : 0 ≤ ρ → ρ ≤ 1 − δ → ∃ N, ρ^N ≤ ε`.  This
   is a routine ~50-line `Q'` induction mirroring `HalfPow`, not yet
   written.  (For the SU(3) point, domination by `(1/2)^Λ` already
   suffices, so this is a generality gap, not a correctness gap.)

2. **The actual lattice-gauge polymer expansion of `⟨o⟩_Λ`.**  The
   engine takes the geometric increment bound as a hypothesis.  Deriving
   that bound from the Wilson-action cluster expansion — defining the
   polymers, the activities, the KP convergence criterion
   `Σ_X |z_X| e^{a|X|} ≤ a(p)` per polymer `p`, and proving the
   boundary-shell increment is geometrically small — is the genuine
   analytic heart and is NOT done.  The `Sheaf/Summability.lean`
   `KPCertificate` structure is still an abstract scaffold (its
   inequality predicate `P` is a parameter); wiring a concrete activity
   into it remains open.

3. **Uniformity in the observable.**  `⟨o⟩_∞` is built for a single
   observable's partial-sum sequence.  The limit functional `o ↦ ⟨o⟩_∞`
   on a whole observable algebra — and its linearity / positivity /
   normalization as a `ProbFunctional` — is not assembled.  This needs
   the increment constant `C` to be controlled uniformly over a class of
   observables (the standard KP "uniform on local observables" estimate).

4. **Tie-in to the `ContinuumMeasure` inverse limit.**  The limit here is
   a per-observable `CReal`; connecting it to `Continuum/ContinuumMeasure`'s
   `InvLim` / `expectation_stable` (so that `⟨·⟩_∞` is the expectation of
   a genuine inverse-limit measure satisfying Kolmogorov consistency)
   is open.  This is the bridge from "limit exists" to "limit is a
   measure."

5. **Interacting measure positivity (OS2).**  Orthogonal to this module:
   reflection positivity of the coupled finite-volume measure is still
   the partial `coneExp_nonneg` result in `Continuum/WilsonFunctional.lean`
   (full Gram-PSD open), as noted in `e2-e3-notes.md`.

### Honest summary

This is a real, self-contained, fully-proved engine: the conversion of a
KP geometric increment bound into a constructive-real infinite-volume
limit with an explicit modulus, demonstrated end-to-end on the canonical
geometric activity.  It is the missing "second half" of the E2 KP item.
The "first half" — deriving the geometric increment bound from the actual
lattice-gauge cluster expansion — and the observable-uniformity /
inverse-limit / positivity tie-ins remain open exactly as listed above.
