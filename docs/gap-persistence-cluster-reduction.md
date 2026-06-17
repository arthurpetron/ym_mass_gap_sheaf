# Gap persistence reduces to one volume-uniform cluster bound (2026-06-17)

Deep-research finding (primary refereed sources) on the two open fields of
`Continuum/ContinuumGapLimit.lean`'s `ContinuumGapPersistence`
(`converges` = the Λ→∞ thermodynamic limit of the finite-volume gap margins;
`floor_persists` = the uniform δ>0 floor / Conj-7.4 tightness fact).

## The decisive distinction: thermodynamic limit ≠ continuum limit

The two fields concern the **thermodynamic / infinite-volume limit at FIXED
lattice spacing** (Λ→∞). This is logically separate from the **continuum limit**
(spacing→0), which is where the genuinely-open Prokhorov/tightness obstruction
lives. Crucially:

- **At fixed spacing, strong coupling, both fields are essentially THEOREMS** in
  the rigorous literature — not conjectures — with explicit volume-INDEPENDENT
  constants.
- The Prokhorov subsequence-extraction landmine does **NOT** contaminate the
  thermodynamic-limit fields. It belongs to the continuum problem, which a
  *lattice* strong-coupling mass-gap existence statement does not need.

## What the literature establishes

- **Osterwalder–Seiler, Ann. Phys. 110 (1978) 440–471**: for lattice YM at
  sufficiently strong coupling the cluster expansion of local-observable
  expectations converges **uniformly in volume**; existence of the mass gap
  (exponential clustering), the infinite-volume limit, and analyticity of
  Schwinger functions all follow. Full proofs in **Seiler, Springer LNP 159
  (1982)**. The gap floor is uniform in Λ *by construction*: the polymer/cluster
  expansion has a volume-independent convergence radius (Kotecký–Preiss /
  Brydges 1986 criterion).
- **Shen–Zhu–Zhu, CMP 400 (2023) 805–851 (arXiv:2204.12737)**: explicit,
  N-uniform constants. Regime `|β| < 1/(16(d−1))` for SU(N) (any d>1, 't Hooft
  scaling βN). Uniform Poincaré constant `K_S > 0` ⇒ Corollary 1.6 mass gap
  with decay rate `c_N` depending only on `K_S, N, d` — explicitly independent of
  volume L. Constructive-flavored: explicit constants, no compactness argument.
- **Brattka–Dillhage, J.UCS 11(12) (2005) 1884–1900**: general bounded
  self-adjoint spectra are only lower-semicomputable, BUT the spectrum map is
  fully computable for COMPACT (a fortiori finite-dim) operators — the rigorous
  backing for our located-gap design. Do not generalize the located argument
  beyond the compact/finite-dim case.

## The single load-bearing lemma

> There exist explicit rationals `ε < 1` and `δ > 0`, depending only on
> `(β, d, group)` and NOT on Λ, such that the cluster expansion of the connected
> two-point function converges with `Σ-of-activities ≤ ε`, yielding exponential
> clustering at rate `≥ δ` uniformly in Λ.

This one bound discharges BOTH fields at once:
- **floor (a):** δ is the volume-independent rational floor.
- **convergence (b):** finite-volume correlators differ from the limit by the
  sum of clusters touching the boundary = `O(geometric)`, i.e. a DIRECT Cauchy
  modulus (no subsequence). The project's route-(ii) geometric-increment CReal
  engine (`crealOfGeoIncrement`) is exactly the device for this.

## Formalization consequence (what to do in Lean)

Collapse `ContinuumGapPersistence`'s two honest fields to ONE literature-backed
obligation — a `UniformClusterBound` (explicit `ε<1`, `δ>0`, geometric tail on
`|gapMargin(Λ) − limit|`) — and CONSTRUCT both `converges` (via the geometric
Cauchy modulus) and `floor_persists` (via δ) from it. The continuum (spacing→0)
limit + its Prokhorov tightness stay the one genuinely-open interface, cleanly
separated from the now-discharged-in-principle thermodynamic limit.

## Landmines

1. Continuum-limit tightness (Prokhorov) does not port constructively — keep it
   out of the thermodynamic-limit chain.
2. Spectrum of general bounded operators is only r.e.; stay in compact/finite-dim.
3. The eigenvalue *sequence* is not computable in general — only finite/compact
   rescues the located second eigenvalue.
4. Non-constructive uniqueness of the infinite-volume state — use the
   cluster-expansion (AHKZ89) or SZZ-coupling constructive uniqueness instead.

Sources: OS78 (Ann. Phys. 110); Seiler LNP 159 (1982); Shen–Zhu–Zhu
arXiv:2204.12737 / CMP 400 (2023); Brattka–Dillhage J.UCS 11(12) (2005);
Brydges "A short course on cluster expansions" (1986); Kotecký–Preiss (1986).
</content>
</invoke>
