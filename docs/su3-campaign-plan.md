# SU(3) Campaign Plan (Phase 10, expanded)

Authoritative plan for extending the constructive mass-gap program from SU(2)
to SU(3): a new paper, extended Lean, extended Python, and an SU(3) lattice
engine. Expands the Phase-10 sketch in `work_plan.md` (Milestones 10.1–10.3)
with the de-risking result below and the engine / campaign / paper tracks that
sketch omits. Milestone IDs here are authoritative for the SU(3) campaign;
where they overlap `work_plan.md` §Phase 10 they supersede it.

---

## 0. Headline: the physics is de-risked (GO)

A non-invasive closure spike (`scripts/su3_closure_spike.py`) fed SU(3) group
constants through the *existing* generic KP/RG machinery (monkeypatching the one
SU(2)-hardcoded function, the large-field character sum) and confirmed the
inductive σ̂-budget **closes for SU(3)** — with more margin than SU(2).

| Quantity | SU(2) (validated baseline) | SU(3) (spike) |
|---|---|---|
| C₂(fund) → small-field c_λ | 3/4 | **4/3** |
| C₂(adj) → one-loop b₀ = (11/3)·C₂(adj) | 22/3 | **11** |
| Convergence window (canonical) | g ≲ 0.42 | **g < 0.485** (large-field-binding) |
| Σ η at g₀ = 0.30, K = 3 | 7.95×10⁻⁴ | **1.21×10⁻⁵** |
| σ̂_K / implied m₀ ≳ √σ̂_K | 0.9992 / 0.9996 | **0.99999 / 0.99999** |
| Budget closes? | ✓ | **✓ for g₀ ≤ 0.45** |

The harness was validated by reproducing the documented SU(2) pilot number
(Σ η = 7.9511×10⁻⁴) on the unpatched pipeline. SU(3) closes harder because the
larger fundamental Casimir suppresses the small-field activity more (smaller
K_sf → smaller η); the faster RG running (b₀ = 11) is a real but sub-leading
headwind over a finite number of steps.

**Implication for sequencing.** The make-or-break analytic risk is retired, so
the campaign is viable and the four pillars can proceed largely in parallel. The
critical path is now *engineering*, not *existence*.

### SU(3) constants of record

- dim(p,q) = (p+1)(q+1)(p+q+2)/2
- C₂(p,q) = (p² + q² + pq + 3p + 3q)/3   [C₂(1,0)=4/3 fund, C₂(1,1)=3 adjoint]
- Large-field weight: Z_t = Σ_{(p,q)≠(0,0)} dim(p,q)²·exp(−t·C₂(p,q))
- μ_plaq = 16, μ_connectivity = log(8e) — dimensional (4D), group-independent
- η-coupling = 0.5 (= c_polymer/A_min) — group-independent

---

## 1. Bottleneck analysis (four pillars)

Ranked by what actually gates the campaign:

1. **Physics-constant closure** — *RETIRED by §0 for the canonical operating
   point.* Remaining: make the SU(3) large-field Z_t a *rigorous* ℚ′-encodable
   bound (the spike uses a high-order truncation). This is the gate on the Lean
   wire-in.
2. **Rust engine (SU(3) lattice)** — the engine is deeply SU(2)-committed
   (quaternion links, Kennedy–Pendleton heatbath, trivial reunitarization).
   Needs Cabibbo–Marinari pseudo-heatbath + CM/QR reunitarization (~550–700 LOC,
   ~1–2 wk). The scaffold (RNG, geometry, sweeps, jackknife, checkpointing,
   binaries, glueball/Wilson *operators*) is group-agnostic; only trace
   extraction and the update kernel change. Validate against known SU(3)
   strong/weak-coupling plaquette expansions.
3. **Python coupling, not file count** — generic modules hardcode SU(2)
   constants in otherwise group-agnostic code. The trap is forking `su3_*`
   copies → drift. Thread one `GaugeGroup` object through the generic modules.
4. **Lean — *not* the bottleneck** — ~1300 LOC of copy-with-new-constants, zero
   new mathlib, identical `decide` proofs. Gated only by the rigorous Z_t (#1).
   Character/Weyl formulas stay in Python by design (need exp/sin).
5. **Naming/organization** — `su2` baked into filenames, `Cargo.toml`,
   `Dockerfile`, `points.tsv`. The repo *anticipates* multi-group
   (`visualizations/pilot/{su2,su3,general}/`, `\SUthree`/`\SUN` macros). Settle
   the convention before the build.

---

## 2. Code strategy — decide per pillar

Per the "parametrize where clean, fork where the math genuinely differs"
decision:

| Pillar | Strategy | Rationale |
|---|---|---|
| Python KP/RG (heat_kernel, {small,large,overlap}_field_kp, sigma_hat, overlap_measure) | **Parametrize** via a `GaugeGroup` object | Already thread c_λ / μ_plaq; only the large-field character sum needs a group hook. Low drift risk. |
| Python rep theory + MCMC kernel | **Fork** (`su3_representations.py`, SU(3) MCMC) | Genuinely different math (irrep labels, Gell-Mann, Haar sampling). |
| Rust update kernel + link type | **Fork behind a `GaugeGroup` trait** | CM heatbath / reunitarization share no code with quaternion SU(2). |
| Rust scaffold (geometry, sweeps, observables, binaries) | **Parametrize** (`--group` flag) | Group-agnostic; trace extraction is a one-line swap. |
| Lean framework (Sheaf, RG, Continuum, Constructive) | **Reuse unchanged** | Already group-abstract. |
| Lean rep/KP/mass-gap | **Fork** (`SU3.lean`, `SU3KP.lean`, `MassGap/SU3.lean`) instantiating a shared `RepData` interface | Mirrors SU(2); new ℚ′ constants only. |
| Paper | **New paper** that `\input`s the shared preamble/class + group-agnostic chapters | Reuse scaffolding, not a fork of the SU(2) `.tex` tree. |

---

## 3. Directory plan

```
computations/
  groups/                 # NEW — parametrization seam
    base.py               #   GaugeGroup dataclass (N, C2_fund, C2_adj, adj_dim, b0, char_sum)
    su2.py  su3.py        #   instances
  su3_representations.py  # NEW — forked rep theory (irreps, Casimir, characters)
  su3_mcmc.py             # NEW — forked MCMC kernel (Gell-Mann, SU(3) Haar)
  <generic modules>       # refactored to accept a GaugeGroup
simulations/src/
  group/{mod.rs,su2.rs,su3.rs}   # NEW — GaugeGroup trait + impls; binaries gain --group
lean/YMGap/
  RepTheory/{RepData.lean, SU2.lean, SU3.lean}
  Sheaf/{SU2KP.lean, SU3KP.lean}
  MassGap/{SU2.lean, SU3.lean}
  RG/{SigmaHatPilot.lean, SigmaHatPilotSU3.lean}
formal-su3/               # NEW paper; \input shared preamble + generic chapters
visualizations/pilot/su3/ # already planned
cloud/points.tsv          # add a `group` column
notes/, tests/            # su3-* companions
```

---

## 4. Milestones

Dependencies in parentheses. ★ = on the critical path to a first SU(3) result.

### Pillar A — Analytic / Python

- **10.1 — SU(2)-specificity audit** *(largely DONE this session)*. The
  four-pillar map + the spike are the audit's payoff. Deliverable: fold this doc
  + `scripts/su3_closure_spike.py` findings into `notes/su-N-extension-audit.md`.
- **10.2 — SU(3) representation theory** (fork). `su3_representations.py`,
  `tests/test_su3_representations.py`, `visualizations/pilot/su3/casimir-spectrum.svg`.
  Acceptance: dims/Casimirs/character orthogonality vs literature.
- **★ 10.4 — Rigorous SU(3) large-field Z_t** (10.2). Replace the spike
  truncation with a rigorous geometric-tail bound over (p,q) irreps, ℚ′-encodable
  like the SU(2) `heat_kernel_character_tail_Z`. Add the `char_sum` hook to the
  `GaugeGroup` seam (10.6-py). Acceptance: bound is provable and reproduces the
  spike's Z_t to working precision.
- **10.3 — SU(3) inductive pilot** (10.2, 10.4). Promote the spike to
  `computations/pilot_su3.py` driven by the `GaugeGroup` object;
  `notes/pilot-su3-results.md` with the g₀ sweep. Acceptance: five-criteria pass
  + budget closure across the documented window.
- **10.6-py — `GaugeGroup` parametrization seam** (10.4). `computations/groups/`;
  refactor the generic KP/RG modules to accept it; SU(2) regression-locked.

### Pillar B — Lean

- **★ 10.5 — Lean SU(3) wire-in** (10.4). `RepTheory/SU3.lean` (Casimirs/dims as
  ℚ′), `Sheaf/SU3KP.lean` (ρ_sf/ρ_lf/K_sf/K_lf from 10.4), `RG/SigmaHatPilotSU3.lean`
  (η/m₀ from 10.3), `MassGap/SU3.lean` (the `decide` witness). Add the
  Python↔Lean lockstep regression (mirror `test_q_lift.py`). Acceptance:
  `#print axioms mass_gap_SU3` clean per AGENTS.md Rule 1.

### Pillar C — Rust engine + lattice campaign

- **★ 10.6-rs — SU(3) engine** (independent). `GaugeGroup` trait + SU(2) (wrap)
  and SU(3) (3×3 complex links, Cabibbo–Marinari heatbath, CM/QR
  reunitarization); trace-extraction swap in observables; `--group` on the
  binaries. Acceptance: plaquette vs known SU(3) strong/weak-coupling expansions;
  SU(2) bit-for-bit unchanged.
- **10.7 — SU(3) lattice campaign** (10.6-rs). `cloud/points.tsv` gains a `group`
  column; an SU(3) β/L grid at matched physical volume; merge + analysis reuse
  the existing GEVP/Cornell/continuum-trend code. Benchmark: continuum
  m(0⁺⁺)/√σ vs the literature SU(3) value (~3.5, *not* Teper's SU(2) 3.74).
  Note the fine-a string-tension systematic from the SU(2) campaign recurs here.

### Pillar D — Paper

- **10.8 — New SU(3) paper** (10.3, 10.5, 10.7). `formal-su3/` reusing the shared
  preamble/class + group-agnostic chapters; new rep-theory/pilot/benchmark
  chapters; SU(3) references. Decision recorded: standalone paper, not a fork of
  the SU(2) `.tex` tree.

---

## 5. Sequencing

```
10.1 (done) ─► 10.2 ─► 10.4 ★ ─► 10.3 ─► 10.6-py
                          └────────► 10.5 ★ (Lean) ──────────┐
10.6-rs ★ (Rust, independent) ─► 10.7 (campaign) ────────────┼─► 10.8 (paper)
                                                              ┘
```

Two independent critical paths: **10.4→10.5** (analytic→Lean) and **10.6-rs→10.7**
(engine→benchmark). They converge only at the paper (10.8). Start 10.2/10.4 and
10.6-rs concurrently.

---

## 6. Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| Rigorous Z_t tail bound harder than SU(2) (2D irrep lattice vs 1D spin) | Med | Sum is dominated by low (p,q); a product-geometric bound over each index is tractable. Spike confirms fast decay. |
| Cabibbo–Marinari reunitarization correctness | Med | Validate against literature plaquette values before production; keep SU(2) as a regression oracle. |
| c_λ = 4/3 inherits the SU(2) fiducial caveat | Low (no *new* gap) | Same rigor as SU(2); flagged, not hidden. Refinement is a shared follow-on. |
| Fine-a string tension systematic (seen in SU(2) campaign) recurs | High | Budget more configs / larger Wilson loops at fine a from the start; carry the `rmax`-window tooling over. |
| `su3_*` forks drift from SU(2) | Med | Parametrize where clean (Pillar A/B framework); fork only rep/kernel; lockstep tests. |
| Faster RG running (b₀=11) erodes margin at large K | Low | Finite-K closure shown with huge margin; infinite-K tail bound is the same deferred constructive-limit step as SU(2). |

---

## 7. Definition of done (first SU(3) result)

A constructive SU(3) mass-gap lower bound m₀ > 0 in units of √σ, with:
(a) `mass_gap_SU3` clean-axiom in Lean (10.5);
(b) a lattice continuum m(0⁺⁺)/√σ benchmark consistent with the literature SU(3)
value (10.7);
(c) the new paper assembling both (10.8).

Spike of record: `scripts/su3_closure_spike.py`. Validated SU(2) baseline:
Σ η = 7.9511×10⁻⁴ at g₀ = 0.30.
