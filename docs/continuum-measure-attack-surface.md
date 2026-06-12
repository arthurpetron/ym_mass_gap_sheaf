# Continuum measure μ_∞ existence — attack surface

A truthful, staged map of the *genuine construction* of the continuum
SU(2) Wilson state μ_∞ that does **not** yet exist in Lean. The deliverable
is a prioritized list of formalizable sub-goals with the first concrete
lemma identified — **not** a claimed solution. The 4D full-rigor existence
+ O(4) restoration is the Clay problem and stays flagged as genuinely-open
mathematics; everything below it is "merely unformalized but standard
(in the convergent regime)."

---

## 0. The honest boundary

There are three tiers, and conflating them is the failure mode this doc
exists to prevent:

- **(C) Clay-open mathematics** — the 4D continuum YM existence with O(4)
  rotation restoration and the *full-coupling* thermodynamic limit. NOT a
  formalization gap; nobody has the proof. Flagged, never "attacked."
- **(P) Project-thesis-open** — the named conjectures the program's
  framework rests on in the *weak-coupling / convergent* regime:
  Conjecture 7.4 (overlap tightness, the KP factor-of-2) and O(4)
  restoration. The program flags these as its honest residue.
- **(S) Standard-but-unformalized** — real analysis that is textbook in
  the convergent regime (Kotecký–Preiss convergence, a positive linear
  functional à la Bishop, reflection positivity of the Wilson action,
  Daniell extension of a consistent tower). This tier is what the attack
  surface below targets: it is genuinely formalizable here.

The current Lean μ_∞ is a tier-(S) shell with the existence content
*absent*: see §1. The construction work is almost entirely in tier (S),
terminating against the tier-(P) conjectures at the RG-transport step.

---

## 1. What exists in Lean, and where existence is absent

### 1.1 The structural shell (DONE, axiom-clean)

`Continuum/ContinuumMeasure.lean` builds the genuine **inverse limit**:

- `ProjectiveSystem M` (per-scale carrier `M k`, coarsening morphisms),
  `is_consistent sys pick` (Kolmogorov consistency, `Prop`),
- `InvLim sys` — the `Σ`-type of consistent threads (MLTT/HoTT-valid),
  with `InvLim.coarsen_proj` proved by `rfl`,
- `ContinuumMeasure M` = `(sys, pick, consistent)`; `.limit = InvLim.ofConsistent consistent`,
  and `pushforward_limit_eq : π_k(μ_∞) = μ_k` proved axiom-free.

`Continuum/ObservableMeasure.lean` instantiates the carrier *concretely*
as a positive normalized functional (the Riesz/moment picture, the right
object for OS reconstruction):

- `ProbFunctional A` — `E : A.carrier → Q'` with `normalized : E 1 = 1`
  and `positive : 0 ≤ E (a* · a)`,
- `ProbFunctional.restrict` — pullback along a unital *-hom, preserves
  positivity + normalization (functional-level Daniell–Kolmogorov
  coarsening),
- `funcProjSystem`, `continuumMeasure`, `expectation_stable` (exact
  per-observable modulus).

### 1.2 Where the existence content is *absent or stubbed*

This is the crux. The shell is real; the **inputs that would make it a
theorem about YM rather than about an arbitrary tower are hypotheses or
toy inhabitants**:

1. **The carrier `M k` / observable algebra is parametric.** `ObsAlg` and
   the per-scale `ProbFunctional` are abstract. The only *inhabitants*
   are `trivFunc` (`E ≡ 1` on `PUnit`) and the stationary character tower
   `charFunc` (a *diagonal, free, single-edge* heat-kernel functional —
   real `Q'` data, but not the interacting lattice measure).

2. **`consistent : is_consistent sys pick` is an input hypothesis.** No
   Wilson family is ever *proved* Kolmogorov-consistent. Every inhabited
   tower (`trivConsistent`, `stationaryConsistent`, `collapseConsistent`)
   gets consistency for free because `incl` is the identity or a collapse,
   so the transport law `E∘map = E` is `rfl` or `1 = 1`. The genuine
   block-spin map (neither identity nor collapse) does not exist
   (`RGTransport.lean` "What remains OPEN").

3. **The positive functional `E` for the interacting measure does not
   exist.** `WilsonFunctional.wilsonCharExp` gives the *single-edge*
   moments and proves positivity **only on the nonnegative-coefficient
   cone** (`coneExp_nonneg`); full PSD (= the heat-kernel measure is
   positive) is open (the all-orders `P_N` problem — see
   `project_pn_wall_dead_ends`, `project_wall2_state`). `PlaquetteReweight`
   builds the reweighted state `E_β = E_w · recip Z` but takes `Ew_pos`
   (= OS2 reflection positivity) and `Z_pos` (= partition function `> 0`)
   as **input fields of `Reweight`**, with the only inhabitant the trivial
   `W ≡ 1, Z = 1`.

4. **The infinite-volume limit is never assembled.** `KPLimit.lean` has
   the *engine* `crealOfGeoIncrement` (geometric increment ⇒ `CReal` limit
   with explicit modulus) — genuine and reusable — but it is only ever fed
   the toy `geoPolymerSum = Σ (1/2)^l`. No actual finite-volume Wilson
   sequence `Λ ↦ ⟨o⟩_Λ` with a *derived* increment bound is plugged in.

5. **OS compliance is signatures-only.** `OSAxioms.OSAxiomBundle` and
   `OSReconstruction.*` carry the five OS axioms and the reconstruction
   quintuple as **abstract `Prop`/`Type` fields**; `os_compliant_su2_measure`
   takes the verifications as inputs. No OS axiom is *read off* a
   constructed `E`.

**Net:** "μ_∞ exists" currently means "an inverse-limit thread exists
*given* a consistent family of positive functionals." The missing content
is the consistent family of *interacting* functionals and their
infinite-volume limit. That is the construction targeted below.

---

## 2. The two construction routes, compared

### Route (i): Projective / Kolmogorov-consistency limit

Build the finite-lattice Gibbs functionals `E_Λ` directly (E1 single-edge
→ E2 product → E2 plaquette-reweighted), prove the tower is
**Kolmogorov-consistent** under block-spin coarsening, and take the
inverse-limit thread. This is exactly the shape of `ContinuumMeasure.lean`.

- **Substrate needed:** (a) the interacting `E_Λ` as a positive normalized
  `Q'`/`CReal` functional — i.e. *full* Wilson PSD positivity (OS2), not
  just cone positivity; (b) the genuine block-spin *-hom `incl_k`; (c) the
  transport law `E_{k+1} ∘ incl_k = E_k` — **this is the load-bearing
  tier-(P) claim** (quantitative σ̂-budget transport, Conj. 7.4); (d) for a
  σ-additive point-set measure (off the OS critical path), Daniell
  extension with a tightness modulus.
- **Gap:** the consistency/transport step (c) *is* the conjecture. Route
  (i) cannot reach μ_∞ without confronting tier-(P) head-on. It is the
  "physically correct" route but its substrate gap includes the open
  conjecture.

### Route (ii): Convergent Kotecký–Preiss cluster expansion

Bypass exact RG consistency: in the convergent regime the *finite-volume
expectations themselves* `⟨o⟩_Λ` form a Cauchy sequence in the volume Λ,
with modulus controlled by KP convergence. The infinite-volume functional
`⟨o⟩_∞ = lim_Λ ⟨o⟩_Λ` is built **directly** as a `CReal`, no consistent
tower required. This is the `KPLimit`/E2 route already seeded here.

- **Substrate needed:** (a) the finite-volume Wilson expectations `⟨o⟩_Λ`
  as `Q'` partial sums (the convergent polymer/character expansion of the
  reweighted measure); (b) the **single-step increment bound**
  `|⟨o⟩_{Λ+1} − ⟨o⟩_Λ| ≤ C·ρ^Λ` with `ρ < 1` from KP activity smallness —
  the analytic heart; (c) a partition-function lower bound `Z_Λ > 0`
  uniform in Λ; (d) positivity/normalization of the limit functional
  (inherited from each `E_Λ` via `CReal` limit-of-nonneg).
- **What is already present:** the **engine** (b)→limit is *done*
  (`crealOfGeoIncrement`, axiom-clean, explicit modulus); the KP *activity
  smallness* `Z_t < 1/16`, `ρ < 1` is present (`SU2KP.lean`,
  `SU3CharFactor.lean`, the Sheaf KP certificates `c_cap_*` with proved
  `ρ,K ≥ 0` and `q < 1`); the reweighting state-law (d) is present
  (`PlaquetteReweight`). The **only missing analytic step is (b)'s
  derivation**: turning the convergent expansion into the per-step
  geometric increment, plus (c).

### Verdict: route (ii) has the smaller constructive substrate gap

Route (ii) does **not** require the genuine block-spin map, exact RG
consistency, or the tier-(P) transport conjecture — it replaces "the tower
is consistent" with "the sequence is Cauchy," which KP convergence gives
*directly* and which the repo already has the engine and the smallness
constants for. Route (i)'s gap *contains* an open conjecture (Conj. 7.4
transport); route (ii)'s gap is tier-(S) only (a standard cluster-expansion
increment bound + `Z_Λ > 0`), modulo the *full* Wilson positivity (OS2)
that **both** routes need anyway. Therefore: **pursue route (ii); reuse the
`KPLimit` engine; treat route (i)'s consistency as a later cross-check, not
the critical path.**

---

## 3. Minimal missing constructive substrate (per route)

Legend: ✅ present · 🟡 partial · ❌ absent.

| Substrate piece | Route | Status | Where |
|---|---|---|---|
| Positive linear functional à la Bishop (`E : A → Q'`, `0≤E(a*a)`, `E1=1`) | both | ✅ | `ProbFunctional` |
| Restriction preserves positivity/normalization | i | ✅ | `ProbFunctional.restrict` |
| `CReal` with explicit modulus; `geRat`/`leRat` order | both | ✅ | `Constructive/Reals.lean`, `ExpPos.lean` |
| KP→limit engine (geometric increment ⇒ `CReal` + modulus) | ii | ✅ | `KPLimit.crealOfGeoIncrement` |
| Constructive reciprocal on positive cone (`recip Z`) | ii | ✅ | `PlaquetteReweight.recip` |
| Reweighting preserves state (`E_β = E_w·recip Z` pos+norm) | ii | ✅ | `PlaquetteReweight.Reweight.functional` |
| Single-edge heat-kernel moments `⟨χ_s⟩_t ≥ 0`, `⟨1⟩=1` | both | ✅ | `WilsonFunctional` |
| KP activity smallness `ρ<1`, `Z_t<1/16`, `q<1` (certificates) | ii | ✅ | `Sheaf/SU2KP.lean`, `SU3CharFactor` |
| **Full Wilson PSD positivity (= OS2 single-edge)** | both | 🟡 cone only | `coneExp_nonneg`; `Pivot2/3` closed, all-N `P_N` OPEN |
| **Finite-volume interacting `⟨o⟩_Λ` as `Q'` partial sum** | ii | ❌ | — |
| **Per-step increment bound `|⟨o⟩_{Λ+1}−⟨o⟩_Λ|≤C·ρ^Λ`** | ii | ❌ | engine ready, input absent |
| **Uniform `Z_Λ > 0` (partition-function lower bound)** | ii | ❌ | `Z_pos` is a hypothesis field |
| Genuine block-spin *-hom `incl_k` | i | ❌ | `RGTransport` "OPEN" |
| Exact RG transport `E_{k+1}∘incl=E_k` (Conj 7.4) | i | ❌ tier-(P) | — |
| Daniell σ-additive extension + tightness modulus | i (optional) | ❌ tier-(S) | off OS critical path |
| OS axioms read off constructed `E` | both | ❌ signatures only | `OSAxioms`, `OSReconstruction` |

The single highest-leverage absent piece on route (ii) is the **per-step
increment bound** (the engine consumes it directly). It depends on full
Wilson positivity only for the *positivity* of the limit, not for its
*existence* — so existence-as-`CReal` can be attacked before PSD closes.

---

## 4. Staged sub-goal list (ordered, with dependencies)

Each stage is a Lean-formalizable obligation. `→` = depends on.

- **S1. Finite-volume reweighted Wilson functional as `Q'` data.**
  Promote `PlaquetteReweight.Reweight` from "`Ew, Z` abstract with `Ew_pos,
  Z_pos` as hypotheses" to a *constructed* `E_Λ` on a real multi-edge
  plaquette algebra, with `Ew(o) = E_⊗(W·o)`, `W = e^{−S_plaq}` built from
  `expNeg`. Reuses `E2ProductFunctional.prodFunctional`. *(tier S)*

- **S2. Partition-function lower bound `Z_Λ ≥ z₀ > 0`, uniform in Λ.**
  `Z_Λ = E_⊗(W) ≥ E_⊗(min W) > 0` since `W = e^{−S} > 0` and the free
  measure is a probability measure. Carry `z₀ : Q'` as data (Rule 2/8).
  → S1. *(tier S)*

- **S3. Finite-volume expectation sequence `S : Nat → Q'`, `S Λ = ⟨o⟩_Λ`.**
  Define `⟨o⟩_Λ = Ew_Λ(o) · recip(Z_Λ)` (reusing `recip`), as a `Q'`
  sequence in the volume index Λ. → S1, S2. *(tier S)*

- **S4. The KP per-step increment bound `|S(Λ+1) − S(Λ)| ≤ C·ρ^Λ`.**
  THE analytic heart: the convergent polymer/cluster expansion of the
  reweighted expectation gives a geometric increment from the activity
  smallness `ρ < 1` (already certified). Produce `(C, ρ)` and the two-sided
  bound as data. → S3 + the Sheaf KP certificates. *(tier S; the genuine
  unformalized analysis)*

- **S5. Infinite-volume functional `⟨o⟩_∞ : CReal` with modulus.**
  Feed S4 into `KPLimit.crealOfGeoIncrement` (with the `ρ = 1/2`
  domination or the general-`ρ` modulus bridge noted in
  `kp-limit-notes.md`). The limit exists as a `CReal`, `approx Λ = ⟨o⟩_Λ`.
  → S4 + the engine (✅). *(tier S; mostly mechanical given S4)*

- **S6. Positivity + normalization of the limit functional.**
  `0 ≤ ⟨a*·a⟩_∞` and `⟨1⟩_∞ = 1` from each `E_Λ` being a state, via
  `CReal` limit-of-nonneg (`geRat`/`ofQ'_le_of_approx_ge`). The
  positivity input is *full* Wilson PSD (OS2) — 🟡; until it closes, this
  stage is conditional on `Ew_pos`. → S5 + (Wilson PSD or `Ew_pos`).
  *(tier S given PSD; PSD itself is the separate `P_N` subproject)*

- **S7. Package as `Continuum*` μ_∞ — a constructive positive normalized
  functional on `colim Obs_k`.** Assemble S5+S6 into the coherent
  infinite-volume `ProbFunctional`-like object (or, on route (i), feed the
  consistency proof into `continuumMeasure`). This is the OS-needed
  *state*. → S5, S6. *(tier S)*

- **S8. Read OS2/OS0 off the constructed `E`.** Replace the abstract
  `OSAxiomBundle` Props for OS2 (reflection positivity = `0 ≤ E(θ(a)*·a)`)
  and OS0 with theorems about the S7 functional. (OS1 invariance, OS3
  symmetry, OS4 clustering-at-rate-σ̂_∞ follow; OS4 ← Track A.) → S7.
  *(tier S, except OS4 rate and O(4) which touch tier P/C)*

**Endpoint:** S7 = "μ_∞ as a constructive positive normalized functional
with explicit modulus"; S8 = "...that is OS-compliant (OS2 read off it)."
The tier-(P)/(C) residue (Conj 7.4 if route (i); O(4) restoration; OS4
rate) is *outside* this list and stays flagged.

---

## 5. The first concrete formalizable lemma

**Name:** `partitionFunction_pos` — *the finite-volume partition function
of the plaquette-reweighted free measure is strictly positive, with an
explicit `Q'` lower bound carried as data.*

This is stage **S2**, and it is first because: (a) it is pure tier-(S)
real analysis (positivity of a finite product of positive heat-kernel
weights — no conjecture); (b) it discharges the `Z_pos` field of
`PlaquetteReweight.Reweight` that is *currently an unproved hypothesis*,
turning the reweighting state-law from conditional into constructed; (c)
the engine, reciprocal, and reweighting machinery downstream all consume
exactly a *positive `Z` with a lower bound*; (d) it needs only
`expNeg`-positivity and `prodE_nonneg`, both present — no PSD, no
increment bound, no block-spin map. It is the smallest brick that converts
a hypothesis field into a theorem.

### Lean shape (Type-level witness data, Rule 2/8)

The witness is the lower bound `z₀` carried as data, not a bare `∃`:

```lean
-- A plaquette Boltzmann weight on n edges as a positive Q' observable,
-- W i = e^{−S i} with S i ≥ 0, so 0 < W i ≤ 1.
structure PlaquetteWeight (n : Nat) where
  W      : Nat → Q'
  W_pos  : ∀ i, (0 : Q') < W i

-- S2: the partition function Z = Π_{i<n} W i is positive, AND we return
-- the explicit lower bound z₀ = Π_{i<n} W i (= Z itself) as DATA.
def partitionFunctionLB {n : Nat} (p : PlaquetteWeight n) :
    Σ' z₀ : Q', (0 : Q') < z₀ ∧ z₀ ≤ E2ProductFunctional.prodE p.W n
```

with the companion theorem `partitionFunction_pos : 0 < prodE p.W n`
(its first projection composed with the bound). The proof is
`prodE`-induction: `prodE W 0 = 1 > 0`; `prodE W (k+1) = prodE W k * W k`,
a product of two positives (`Q'.mul_pos` from `W_pos`). The `Σ'` keeps the
bound `z₀` computable, per Rule 8.3.

**File it extends:** `Continuum/PlaquetteReweight.lean` — it directly
feeds the `Z` / `Z_pos` fields of `Reweight`, replacing the trivial
`Z = 1` inhabitant with a genuine positive partition function. (It also
reuses `E2ProductFunctional.prodE`/`prodE_nonneg`.)

**Skeleton:** stated statements-only in
`Continuum/ContinuumExistence.lean` (NEW), with the S1–S8 obligations as
honest `sorry`s logged `-- SORRY[continuum]: ...` per Rule 6. That file
imports `Continuum.PlaquetteReweight` and `Continuum.KPLimit` and does
NOT touch `YMGap.lean`.

---

## 6. What stays genuinely open (the truthful residue)

- **(C) 4D existence + O(4) rotation restoration** — the Clay problem.
  Not on any stage list. The σ̂-trajectory thesis claims the convergent
  regime only; O(4) restoration is flagged at E3/E4 and never "attacked."
- **(P) Conjecture 7.4 (overlap tightness) and exact RG transport** — the
  load-bearing project conjecture for route (i). Route (ii) avoids it for
  *existence* but the program still owes it for the full RG picture.
- **(P/S) Full single-edge Wilson PSD positivity (OS2)** — the all-N
  `P_N` nonneg-coefficient problem; research-novel uniform step, cone
  positivity + `N ≤ 3` closed. Needed for the *positivity* (not the
  *existence*) of the limit (stage S6).
- **(S, large) OS reconstruction operator layer** — Stone's theorem,
  unbounded self-adjoint spectral calculus on constructive reals (B3).
  Standard but a major separate build-out; downstream of S7/S8.

The value of this map is that stages S1–S5 (existence of μ_∞ as a `CReal`
functional in the convergent regime) are tier-(S) and reachable with the
engine already in hand; only S6's positivity and the OS4 rate / O(4)
touch the open tiers.
