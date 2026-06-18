# Inhabiting `physGapMin>0` for 4D YM — research synthesis & plan (2026-06-18)

Three deep-research strands (frontier / stepping-stones / formalization-path) on whether
and how to inhabit the open Lean obligation `RegScalingBand.physGapMin>0` — the physical
gap `Δ = liminf_{a→0} m_lat(a)/a > 0` (dimensional transmutation).

## The blunt verdict (all three strands agree)

Inhabiting `physGapMin>0` UNCONDITIONALLY for 4D YM **is the Clay problem** — not in reach.
The two rigorously-proven endpoints sit on opposite sides of an uncontrolled crossover:
- **Strong coupling / fixed spacing:** positive gap PROVEN (Osterwalder–Seiler 1978;
  Shen–Zhu–Zhu CMP 400 (2023), explicit β-thresholds e.g. SU(N) |β|<1/(16(d−1)),
  log-Sobolev+Poincaré). Fixed lattice, NOT uniform in a.
- **Weak coupling / continuum:** Balaban UV stability (CMP 109/116/122, 1987–89) — bounded
  effective action uniformly in the UV cutoff, the closest to rigorous 4D asymptotic
  freedom; but only a SUBSEQUENCE (no uniqueness), no OS axioms, NO spectral/gap analysis.
  IR completion open. Magnen–Rivasseau–Sénéor (CMP 155, 1993): SU(2) UV cutoff removed but
  IR cutoff FIXED (gap lives in the IR — untouched).
Nobody has bridged them. Tools that would propagate a gap are absent at d=4: no FKG/Griffiths
for non-abelian links; Bakry–Émery Γ₂ not uniformly bounded below as β→∞ (so the
Bauerschmidt–Dagallier lattice-uniform LSI — proven for scalar φ⁴₂/₃, NOT YM — does not
transfer); strong-coupling expansion has finite radius and diverges across the crossover;
d=4 is marginal (logarithmic β, ξ ~ exp(1/2β₀g²) diverges).
Discredited/unverified (do NOT cite as evidence): Jacobsen SU(3) arXiv:2506.00284 WITHDRAWN
by arXiv 2025-06-13; Lim arXiv:2307.00788 (no journal, 7 revisions); viXra 2602.0041;
INSPIRE 3124506 ("gap persists across RG blocks" — on-target CLAIM but unverified, a lead).

## Two genuine, buildable wins (short of the Clay summit)

### Win 1 — CONDITIONAL inhabitant (strands frontier + path converge)
Name the single recognized estimate `E` and reduce `physGapMin>0` to it:
> **UniformTransferGapAlongAF.** For the reflection-positive Wilson transfer Hamiltonian
> H(a) of pure SU(N) YM₄ (infinite volume, bare coupling on the two-loop AF trajectory
> a·Λ_L = exp(−1/2β₀g²)·(β₀g²)^{−β₁/2β₀²}), there exist c>0, a₀>0 INDEPENDENT of a with
> a·gap(H(a)) ≥ c for 0<a<a₀. Hence Δ = liminf m_lat(a)/a ≥ c·Λ_L > 0.
Cheapest sufficient lemma `RGGapPersistence`: the per-block transfer-gap multiplier survives
one block-spin RG step with a scale-independent factor, ∏ρ_k ≥ c > 0 across the scaling
window — exactly the strong-coupling↔continuum bridge Balaban stops short of.
**Lean shape (strand path):** a `UniformGapEstimate`/`UniformTransferGapAlongAF` structure
between `RegScalingBand` and `RegScalingLimitModulus`; the bridge `E ⇒ physGapMin>0` is pure
assembly over `Q'.divPos` + `ofQ'_le_ofQ'` + `band_gap_survives` (no new analysis). Turns
"no inhabitant" into "inhabitant modulo one named theorem-shaped conjecture" — the posture
of every refereed survey (Douglas, Nat. Rev. Phys. 8 (2026) 86; Chatterjee arXiv:1803.01950).
Unconditional sub-pieces ALREADY done: strong-coupling fixed-spacing anchor
(`ClusterGapReduction`), `divPos`/dimensionless reduction, floor→survival lift.

### Win 2 — GENUINE PoC inhabitant: 2D Yang–Mills area law (stepping-stones strand)
2D YM (Driver CMP 123 (1989); Sengupta Mem. AMS 600; Lévy Mem. AMS 790 + Astérisque 388)
is exactly solvable with a rigorously-controlled continuum limit. The area-law string
tension `σ_R = ½ g² C₂(R) > 0` is closed-form and **spacing-uniform by an EXACT RG fixed
point** (the heat-kernel/Migdal action is self-reproducing under blocking ⇒ the observable
is constant in n, modulus trivial). Buildable on OUR primitives: `C₂ = 3/4` for SU(2)
fundamental already in `RG/SUNWeylData`; positivity via `divPos`.
**Lean inhabitant of a `RegScalingBand`-analog:** spacing `a_n = a₀/2^n`; observable
`W_n = exp(−½ g² C₂ A)` constant in n (exact fixed point); uniform floor `σ_R = ½g²C₂ > 0`
spacing-independent; modulus trivial. The FIRST genuinely-PROVEN (not assumed) positive
floor uniform in a — validates the `RegScalingBand` plumbing end to end.
**Honest caveat:** 2D YM has no propagating d.o.f.; `σ_R` is a string tension, NOT a
transfer-operator spectral gap, and the value is put-in via (g², C₂). It demonstrates the
ARCHITECTURE, not mass-GENERATION (the actual 4D difficulty). For a faithful spectral-gap
inhabitant (still mass-input) the target is φ⁴₂/₃ via Shen–Zhu–Zhu/Helffer–Sjöstrand — but
that needs Markov-semigroup/LSI machinery absent from our stack (high cost).
φ⁴ caveat: it's the DYNAMICS (Langevin LSI/Poincaré) gap, bridged to a static gap via
Helffer–Sjöstrand (JSP 74 (1994) 349); mass is INPUT (bounded susceptibility = off-critical).

## Plan of action (prioritized)
- **Step 1 (low-risk, high-value):** build the CONDITIONAL inhabitant —
  `UniformTransferGapAlongAF` + `RGGapPersistence` sufficient lemma + the `E ⇒ physGapMin>0`
  bridge (assembly over divPos/existing lemmas). Sharpens the open field to a recognized
  conjecture. File: RegularContinuumPipeline.lean (+ maybe a new module).
- **Step 2 (parallel, genuine PoC):** build the 2D YM area-law `RegScalingBand` inhabitant
  (new module, e.g. Continuum/TwoDYangMills.lean) — first PROVEN spacing-uniform positive
  floor. Reuse SUNWeylData C₂, divPos. Independent of Step 1 (different files) → parallel.
- **Step 3 (optional, small):** close the deferred band-edge equality-collapse lemma
  (running-fold-of-Cauchy-converges) to upgrade `band_brackets_gap` to `band_collapse_edges`.

Sources: Osterwalder–Seiler Ann.Phys.110(1978); Seiler LNP159(1982); Balaban CMP
109/116/122(1987–89); Magnen–Rivasseau–Sénéor CMP155(1993); Shen–Zhu–Zhu CMP400(2023,
arXiv:2204.12737); Chandra–Chevyrev–Hairer–Shen Invent.237(2024); Chatterjee arXiv:1803.01950,
2401.10507; Bauerschmidt–Dagallier CPAM77(2024, arXiv:2202.02295) [φ⁴/Ising, NOT YM];
Helffer–Sjöstrand JSP74(1994)349; Driver CMP123(1989); Sengupta Mem.AMS600(1997); Lévy
Mem.AMS790(2003)/Astérisque388(2017); Göpfert–Mack CMP82(1982)545 [cautionary: 3D U(1) gap
is a lattice artifact, a→0 gives free photon]; Douglas Nat.Rev.Phys.8(2026)86.
Flagged withdrawn/unverified: arXiv:2506.00284 (withdrawn), 2307.00788, viXra:2602.0041,
INSPIRE 3124506.
</content>
