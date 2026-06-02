# Tightening Ch. 17–20: audit + punch-list

Audit of the continuum / OS / mass-gap chapters against the reviewer items
(a) projective limit + tightness, (b) full OS at continuum, (c) OS
reconstruction + Stone. No `.tex` edited yet — this is the sign-off
document before rewriting.

Files audited in full: `continuum-measure.tex` (Ch. 17),
`os-axioms.tex` (Ch. 18), `os-reconstruction.tex` (Ch. 19),
`mass-gap-theorem.tex` (Ch. 20), plus `sigma-hat-trajectory.tex` (Ch. 13)
and the glossary for the σ̂ definition.

---

## 0. CENTRAL FINDING — the √σ̂_∞ vs σ̂_∞ inconsistency (gates all Ch. 18–20 edits)

**Definition (Ch. 13 eq. 13.1, glossary):** `σ̂_k := a_k²·σ_k` is the
**dimensionless string tension** governing the Wilson-loop *area* law
`⟨W(C)⟩ ≤ C_R·exp(−σ_k·A(C))`. It is a 1/length² quantity (per unit area),
*not* a mass (1/length).

The mass-gap rate is stated **three mutually inconsistent ways**:

| Location | Statement | rate |
|---|---|---|
| Ch. 17 Prop. `area-law-mu-infinity` | area law under μ_∞ | σ̂_∞ (string tension) ✓ correct kind |
| Ch. 18 Thm. `os4` (OS4 cluster) | `\|⟨FG⟩−⟨F⟩⟨G⟩\| ≤ C·exp(−σ̂_∞·d)`, d a distance | **σ̂_∞, no √** ✗ |
| Ch. 19 Thm. `cluster-to-gap` | "`m_0 := σ̂_∞`", `m ≥ m_0 = σ̂_∞` | **σ̂_∞, no √** ✗ |
| Ch. 20 Lemmas `os4-cluster`, `cluster-to-gap` | restate `m ≥ m_0^(OS4) = σ̂_∞` | **σ̂_∞, no √** ✗ |
| Ch. 20 composition proof (lines 226–233) | silently switches to `m ≥ ε^{1/2} = √σ̂_∞` | **√σ̂_∞**, via a *wrong* justification |
| Ch. 20 explicit bounds (Prop. `m0-canonical/wilson`) | `m_0 = 999/1000`, verified by `m_0² ≤ ε` | **√σ̂_∞** (headline uses the √) |
| `mass-gap-discussion.tex` | `m ≥ √σ̂_∞`, with the ~3.7 looseness factor | **√σ̂_∞** ✓ |
| glossary | σ̂_∞ = string tension; m_0 = spectral gap (distinct quantities) | — |

**Two distinct problems:**

1. **Dimensional conflation.** Ch. 18 OS4 writes `exp(−σ̂_∞·d)` with `d` a
   distance. A cluster/mass rate is 1/length; σ̂_∞ is a string tension. The
   cluster property's decay rate is a *mass*, and identifying it with the
   string tension is dimensionally wrong (unless everything is read in
   lattice units, which then hides the physics).

2. **The √ appears from nowhere, with an incorrect justification.** Ch. 20
   lines 226–231 introduce `m ≥ ε^{1/2}` via "units of mass not
   mass-squared … E = t⁻¹". This is wrong: the spectral gap of H_op
   *already is* a mass (natural units), so no √ comes from unit conversion.
   The √ is the physical **string-tension → mass-gap relation** (`m ≳ √σ`),
   which is a *separate analytical input*, not a unit change — and it
   directly contradicts the `cluster-to-gap` lemma (Step 3) it is composing,
   which had just claimed `m ≥ σ̂_∞` with no √.

**Net:** the final headline (`m_0 = 0.999` from `m_0² ≤ σ̂_∞`) and the
discussion chapter agree on `m ≥ √σ̂_∞`. But Ch. 18 OS4, Ch. 19
cluster-to-gap, and the two Ch. 20 intermediate lemmas all assert
rate/gap `= σ̂_∞` (no √), contradicting both the headline computation in
the same chapter and dimensional analysis.

**A reviewer hits this immediately** — it is exactly the "spectral
injection is the payoff — make it ironclad" item.

### Resolution options (author decision needed — this is the math, not typesetting)

- **Option A (recommended): make the area-law→mass-gap √ a single named,
  cited, dimensionally-honest bridge.** Keep σ̂_∞ as a string tension
  everywhere. State OS4 (Ch. 18) as the *connected-correlator / area-law*
  statement the polymer expansion actually delivers (rate σ̂_∞, a string
  tension). Then insert ONE explicit theorem — the
  *area-law(string-tension)→spectral-gap* relation `m ≥ √σ̂_∞` (in units
  σ_0 = 1) — as the cluster-to-gap bridge, citing the standard relation
  (the chapter already cites BF81 for "sharper mass-gap-from-clustering").
  Delete the incorrect "units E = t⁻¹" paragraph; the headline
  computation `m_0² ≤ σ̂_∞` is already correct and stays.

- **Option B: keep the abstract OS cluster-to-gap lemma general** (`m ≥
  m_cluster` for a genuine mass-scale cluster rate `m_cluster`, no √ — this
  is the *correct* general OS theorem) **and identify `m_cluster = √σ̂_∞`**
  upstream via the area-law bridge. Same √, placed one step earlier.

- **CAVEAT for both:** the relation `string tension > 0 ⟹ mass gap ≥ √σ`
  is **not a general theorem** — area law (confinement) and a spectral gap
  are logically distinct. What the polymer/KP expansion *rigorously*
  controls is exponential clustering of local gauge-invariant observables
  at the **KP convergence rate ρ_∞**, which may be the honest cluster rate
  (not σ̂_∞ and not √σ̂_∞). **Determining which rate the machinery actually
  delivers requires auditing the Ch. 7 polymer/KP cluster bound** and is a
  genuine mathematical-intent decision. Recommend this audit before
  committing to A vs B.

### AUDIT RESULT (Ch. 7 / KP machinery) — Option A confirmed

Read `sheaf-framework.tex` §7 (polymer expansion + KP datum), `small-field-kp.tex`,
`large-field-kp.tex`, `overlap-kp.tex`.

- The KP convergence rate is `ρ_sf(g_k) = c_λ·κ_conv / g_k² = (3/4)/g_k²`
  (canonical), with `ρ_∩ = min(ρ_sf, ρ_lf)`. As the flow goes UV-ward
  (`g_k → 0`), `ρ_sf → ∞` in lattice units. So the KP/cluster rate **diverges**
  in the UV — it is the lattice-unit correlation rate (correlation length → 0 in
  lattice spacings as `a_k → 0`), exactly as expected, and is **not** a finite
  mass. ⟹ "honest rate = ρ_∞" is ruled out: ρ_∞ is not finite.
- The only quantity the machinery tracks to a finite positive limit is the
  **dimensionless (RG-invariant) string tension** `σ̂_k = a_k²σ_k → σ̂_∞ ≈ 0.999`.
  σ̂ is RG-invariant under pure dimensional rescaling; the η-budget perturbs it
  by a summable amount.
- Therefore the mass gap **must** come from σ̂_∞ via the area-law→mass-gap
  relation `m ≥ √σ̂_∞` (in σ_0 = 1 units). **The √ is mandatory and is a genuine
  physical (confinement) relation, not a unit conversion.**
- **Self-consistency check:** with the conservative constant `c = 1` in
  `m ≥ c√σ`, the bound is loose relative to the true `m/√σ ≈ 3.74` (Teper) by
  exactly the ~3.74 factor the discussion chapter already reports. So `c = 1` is
  the intended conservative choice and the √ structure is internally consistent
  with the existing sharpness discussion.

**Decision: Option A.** σ̂_∞ stays a string tension everywhere. The √ becomes one
named, cited bridge theorem (`m ≥ √σ̂_∞`, c = 1, cite Seiler / Simon §6 / BF81;
the constant is where the looseness lives). OS4 (Ch. 18) and cluster-to-gap
(Ch. 19) are corrected so the cluster/gap rate is the mass `m` (related to σ̂_∞
by the bridge), not σ̂_∞ directly. Ch. 20's "units E=t⁻¹" paragraph is deleted
and replaced by the bridge; the headline `m_0² ≤ σ̂_∞` computation is unchanged.

### STATUS — §0 CLOSED (2026-06-02)

Most of Option A was already applied in commit `4ae7586` (`[paper] Tighten
Ch.17-20: dimensionally-honest mass-gap chain`), which post-dates this note's
audit. Current state verified file-by-file:

- `os-axioms.tex` Thm `os4` — rate is a mass `m`, `m ≥ √σ̂_∞` via the bridge,
  with a dedicated dimensional remark. ✓
- `os-reconstruction.tex` — `cluster-to-gap` is stated GENERICALLY (gap ≥
  cluster rate `m_c`, no √); the √ lives only in the named, cited bridge
  theorem `thm:area-law-to-gap-bridge` (`m_c ≥ √σ̂_∞`); `cor:gap-from-sigma`
  composes them. ✓
- `mass-gap-theorem.tex` — composition gives `m ≥ √σ̂_∞ ≥ √ε`, headline
  `m_0² ≤ ε`; the wrong "units E=t⁻¹" paragraph is gone, replaced by an
  explicit "the √ is dimensional content, not a unit change" note. ✓

Two residual spots the `4ae7586` sweep MISSED, fixed in this commit:

- `continuum-measure.tex` `rem:bridge-mass-gap` — still said "identifies the
  mass gap with the exponential-decay rate σ̂_∞ … spectral gap ≥ σ̂_∞" (bare,
  no √). Rewritten to `gap ≥ √σ̂_∞` via `\cref{thm:area-law-to-gap-bridge}`.
- `appx-roadmap.tex` sharper-decay item — called σ̂_∞ "the OS4 cluster rate"
  (it is the string tension; the cluster rate is the mass `m`) and wrote the
  sharper bound as `m ≥ c·σ̂_∞` (dimensionally wrong). Fixed to `m ≥ c·√σ̂_∞`.

Full-paper grep now shows σ̂_∞ used only as an area-law (string-tension) rate
or under a √; no surviving bare-σ̂_∞ gap/cluster statement. `latexmk` resolves
both new cross-refs (the pre-existing multiply-defined-label / 1-missing-citation
warnings are unrelated document hygiene, out of §0 scope).

---

## (a) Ch. 17 — continuum projective limit + tightness  [cleanly closeable]

**What's already fine:** tightness is *genuinely trivial* — each
Ω_k = SU(2)^{E_k} is compact (Prop. `tightness`), so the tightness modulus
is identically zero. That is the correct answer for a compact gauge group
and is worth stating explicitly as the modulus (the reviewer's "explicit
modulus of tightness" — it's 0, and here's why: compactness of SU(2)).

**The actual soft spot — Prop. `area-law-mu-infinity` proof:** it says
"…at every finite scale k … taking the limit k → ∞". This limit is
hand-waved. Fix with the **monotonicity argument**: σ̂_k is decreasing in k
with σ̂_k ≥ σ̂_∞ (Ch. 15 / Ch. 13 budget), so the scale-k bound
`⟨W⟩_{μ_k} ≤ C·exp(−σ̂_k·A) ≤ C·exp(−σ̂_∞·A)` holds with the *uniform*
weaker rate σ̂_∞ at every k, and a loop resolved at scale 0 has
`⟨W⟩_{μ_∞} = ⟨W⟩_{μ_0}` *exactly* (consistency, Cor. `cylindrical`) — no
limit needed.

**Explicit rate (the reviewer's "concrete rate"):** give
`|σ̂_k − σ̂_∞| ≤ Σ_{j≥k} η_j ≤ η_k / (1 − r_uv^∞)` from the Ch. 15
geometric tail (Cor. `tail-bound`), with `r_uv^∞ ≈ 0.976`. This is a
concrete, citable convergence modulus for the σ̂_∞ injection.

**Effort:** ~1 short subsection rewrite + 1 explicit-rate corollary. No
dependency on the §0 decision.

---

## (b) Ch. 18 — full OS at the continuum  [partly closeable, O(4) stays open]

1. **O(4) — do NOT fake it.** Full rotation-invariance restoration is a
   real research program (MRS93-level). The chapter is right to flag it
   open. **Rigorous tightening:** prove the **reduced-axiom-set theorem** —
   the mass-gap reconstruction needs only {OS0, *time-translation*
   invariance, reflection positivity through *lattice time-planes*, OS4}.
   It does **not** need O(4) or even spatial rotation. This "proves a
   weakened version sufficient for the gap" exactly as the reviewer asks,
   and demotes O(4) to an explicit non-critical-path item. (Currently the
   chapter asserts this in prose — "the mass-gap statement does not depend
   on this O(4) refinement" — but never states/proves it as a theorem with
   the precise axiom subset. Make it a numbered theorem.)

2. **Reflection positivity at ∞ — separate exact from approximate.** OS2
   for the *time-zero lattice-plane* reflection is **exact** at every scale
   and lifts by consistency (Cor. `cylindrical`) with no limiting argument.
   The current Thm. `os2` lumps this together with arbitrary
   off-lattice reflections (which need an approximation argument and really
   belong with the O(4) item). Split into: (i) exact lattice-plane RP — all
   the reconstruction needs; (ii) general-reflection RP — defer with O(4).

3. **OS4 — see §0.** Its rate is the load-bearing mass-gap input and is
   where the √ inconsistency lives. The proof is a sketch citing GJ §20.1;
   it is honestly *conditional on the Ch. 7 KP certificates* (the open
   [P2.1] obligations). Tighten the *reduction* (OS4 ⟸ KP certificates +
   §0 rate decision) and state the conditionality plainly.

---

## (c) Ch. 19 — OS reconstruction + Stone  [tightenable; contains one real bug]

1. **BUG — Prop. `T-contraction` proof is wrong as written.** The
   "F = F⁺ + F⁻ … quadruple half-space x⁰ ≥ 3t/2" decomposition does not
   give the contraction and is not the standard argument. Replace with the
   correct Glimm–Jaffe step: for t ≥ 0,
   `‖T_t[F]‖² = ⟨F, T_{2t}F⟩_OS` (using θT_t = T_{−t}θ + translation
   invariance), then Cauchy–Schwarz `⟨F, T_{2t}F⟩ ≤ ‖F‖·‖T_{2t}F‖` and a
   standard iteration/`a_n = ‖T_{2^n t}F‖` argument gives `‖T_t[F]‖ ≤ ‖F‖`.

2. **Stone self-adjointness — make U_t = U_t* explicit.** The text asserts
   "self-adjointness is automatic from U_t* = U_t" but U_t is a *semigroup*
   (t ≥ 0), not a group. Self-adjointness of the generator −H needs the
   semigroup to be **symmetric** (U_t = U_t*), which follows from the
   θ-symmetry of the Schwinger form. State and prove U_t = U_t* as a short
   lemma, then Stone/Hille–Yosida gives a unique self-adjoint H ≥ 0. This
   makes the reviewer's "self-adjoint H_op spelled out carefully" ironclad.

3. **Spectral injection (Thm. `cluster-to-gap`) — the payoff.** The
   Källén–Lehmann sketch is the right idea. Make it ironclad: define the
   spectral measure `dμ_{F,F}(E)` for F ⊥ Ω, write
   `⟨F, U_t F⟩ = ∫₀^∞ e^{−tE} dμ_{F,F}(E)`, and read off
   `inf supp dμ_{F,F} ≥ (cluster rate)` from the large-t decay. This step
   is *correct as a general OS theorem only if it is fed a genuine
   mass-scale cluster rate* — i.e., it is the consumer of the §0 decision.
   Keep this lemma general (rate → gap, no √) and let §0 fix what rate is
   fed in.

4. **References (reviewer asked for these explicitly):** the chapter
   already cites GJ87 §6.1, OS73/75, Reed–Simon II (X.47a, X.49), Sim74 §6.
   That's the right standard-treatment set; add precise theorem pointers in
   the two proofs above (RS-II X.47a for the symmetric-semigroup generator;
   GJ §6.1 for the contraction).

---

## Smaller findings

- Ch. 20 lines 226–231: the "units E = t⁻¹ ⟹ m ≥ ε^{1/2}" paragraph is the
  incorrect justification of the √ (see §0). Replace, don't patch.
- Ch. 18 Thm. `O4-restoration` "Scope" paragraph cites an appendix
  "(omitted in this version)". Either include the R_k-approximation sketch
  or drop the forward-reference to an omitted appendix (a reviewer reads
  that as a hole).
- Cross-chapter: once §0 is resolved, the glossary entry (σ̂_∞ = string
  tension, m_0 = gap) and the discussion-chapter `m ≥ √σ̂_∞` should be the
  single source of truth that Ch. 18–20 are made consistent with.

---

## Recommended order of execution (after §0 decision)

1. Audit Ch. 7 KP cluster bound → decide §0 Option A vs B and the honest
   cluster rate (σ̂_∞ / √σ̂_∞ / ρ_∞).
2. Ch. 19 bug fix (`T-contraction`) + Stone symmetry lemma — independent of §0.
3. Ch. 17 explicit-rate / tightness-modulus — independent of §0.
4. Ch. 18 reduced-axiom-set theorem + RP split — independent of §0.
5. Thread the §0 rate decision through Ch. 18 OS4 → Ch. 19 cluster-to-gap →
   Ch. 20 composition, deleting the incorrect "units" paragraph.
6. Rebuild, verify cross-refs, check the headline m_0 computation is
   unchanged.
