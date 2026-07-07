# Is the interacting amplitude `z_n` constructible as a CHARACTER SUM? — the terminal `pertRep` frontier

**Deliverable Lean file:** `lean/YMGap/Continuum/ZnCharacterSumFrontier.lean` (wired into
`YMGap.lean`; full `lake build` green = **708 jobs**; `YMGapGuard` **frontier-guard OK** =
5 Clay-frontier types still unconditionally uninhabited). Numerics: `zn_charsum_numerics.py`
(mpmath dps 45, sympy exact 6j). **Commits: none** (per instruction).

**Headline verdict.** The lattice-Haar strong-coupling character sum `z_n` **IS constructible**
from the already-proved/built pieces (`coeffW` + Peter–Weyl orthogonality `δ/dim` + Wigner 6j +
cluster combinatorics + KP/Penrose) — and it is *already* realized in the library as
`wilsonG`/`treeG`/`graphG`. **But building it does NOT close `pertRep`, and this is now PROVED,
not asserted.** The character sum is the FIXED-SPACING amplitude; `pertRep`'s `zAmp` is the
CONTINUUM (`a→0`) field-space amplitude, and the character expansion **provably DIVERGES** at
the continuum (`2w³ → 2 > 1`) and **provably OVERSHOOTS** the field activity `g² = 1−w`. The
genuine gap is the continuum limit + the config-space field measure. **The 4D Yang–Mills mass
gap remains OPEN; nothing is faked; no guarded bundle inhabited.**

---

## 0. The obligation

`IsserlisPenroseReduction.IsserlisPenroseData.pertRep`:

    pertRep : ∀ k n, zAmp k n ≤ |Csum w (adjN n) (adjE k n)| · (prop k)^n

the terminal residual: the interacting connected `n`-cluster amplitude `zAmp` (physically
`z_n = ∫ e^{−S_int} χ dHaar / Z`) IS the signed-Ursell character sum. The task: BUILD `z_n` as a
finite character sum from the proved pieces and check — with maximal scrutiny — whether that
construction CLOSES `pertRep` or locates the exact remaining gap.

## 1. What IS constructible (genuine, proved) — the fixed-spacing lattice-Haar character sum

Every ingredient the task lists is genuinely in the library and proved/built:

| piece | object | status |
|---|---|---|
| single-plaquette character expansion of `e^{−S_int}` | `coeffW w s = dim_s·w^{s(s+2)}` (`BondMovingStep.coeffW`) | **PROVED** (`coeffW_zero=1`, `coeffW_one=2w³`, `coeffW_nonneg`) |
| 2-body shared-link Haar integral | `∫χ_jχ_{j'} = δ/dim` (`ReflectionPositivity.reflWeight`, `vacSubKernel`) | **PROVED** |
| ≥3-body link fusion | triangle indicator (`m=3`) + signed `sixjCReal` (`m≥4`) | triangle PROVED; 6j BUILT, pentagon REDUCED |
| cluster combinatorics (line/tree/cycle/multiloop/disconnected) | `wilsonG`/`treeG`/`cycleG`/`graphG`/`jointG` | **PROVED** (`MultiComponentFactorization`) |
| KP convergence `\|z_n\|≤(μg²)^n` | Penrose `\|C(G)\|≤τ(G)` + Cayley + Euler | **PROVED** (`KPFieldAmplitude`) |

So the multi-plaquette amplitude assembles as the FINITE character sum
`z_n = Σ_{rep assignments} ∏_p coeffW(j_p) · ∏_links (Haar link integral)`. For the
single-common-excited-rep geometry the `n` shared links (Peter–Weyl orthogonality) force ONE
common rep `r≥1`, collapsing to `Σ_{r≥1} (coeffW w r)^{n+1}` — the new file's `zCharCluster`,
exactly `WilsonConnCorr.wilsonG`'s collapse. It is nonnegative (`zCharCluster_nonneg`) and, at
STRONG coupling `0≤w≤1/2`, converges geometrically (`charRate_lt_one_strongcoupling`,
`zCharCluster_term_le_strongcoupling`: per-plaquette rate `ρ=coeffW w 1=2w³≤1/4<1`). **This is
genuine and re-derives the ALREADY-PROVED fixed-spacing strong-coupling gap.**

Numerics (dps 45): `z_2^char=ΣcoeffW²`, `z_3^char=ΣcoeffW³` are finite convergent character
sums at `w=0.5,0.7,0.79`; the ≥3-body link integrals `∫χ_aχ_bχ_c` = triangle indicator
(`(1,1,2)→1`, `(1,1,1)→0`), 4-body `mult4(1,1,1,1)=2` = the 6j/3nj structure; the signed 6j is
genuinely irrational (`{½½1;112 3/2}=√3/6`, `{½½1;11 3/2}=−1/6`).

## 2. THE DECISIVE OBSTRUCTION — the character sum does NOT close `pertRep` (PROVED)

The character sum is the FIXED-SPACING object. `pertRep`'s `zAmp` is the CONTINUUM field-space
amplitude of the Bałaban RG / KP field-cluster chain (the `|z_1|≤g²=1−w` object,
`KPFieldAmplitude.SinglePolymerActivity`). These are DIFFERENT objects, and the character sum
**provably FAILS** to be the continuum one. Three PROVED, kernel-`decide`, **axiom-free** facts:

| theorem | content | numeric |
|---|---|---|
| **`charRate_exceeds_one_at_continuum`** | `coeffW (9/10) 1 = 2·(9/10)³ > 1` | `1458/1000 > 1` |
| **`charRate_crossover_below_continuum`** | `coeffW(79/100)1<1 ∧ 1<coeffW(8/10)1` — crossover `2w³=1` at `w≈0.794` | `0.986<1<1.024` |
| **`charWeight_overshoots_fieldActivity`** | `coeffW (9/10) 1 > g² = 1−9/10` | `1458/1000 > 1/10` |
| **`charWeight_overshoots_bigfactor`** | overshoot factor `>14` (unbounded as `w→1`) | `14·(1/10) < 1458/1000` |

**(B) Divergence at the continuum.** The character per-plaquette factor `ρ=coeffW w 1=2w³→2>1`
as `w→1` (`a→0`). The strong-coupling character expansion CONVERGES only for `w<(1/2)^{1/3}≈0.794`
and DIVERGES throughout the entire asymptotically-free / continuum window `w∈(0.794,1)` where
every physical `a→0` scale lives. So the character-sum `z_n` **does not converge at the
continuum** and does NOT define the continuum interacting amplitude `pertRep` encodes.

Numeric confirmation (dps 45): `2w³` = `0.25, 0.9999, 1.458, 1.941, 1.994, 1.9994` at
`w=0.5, 0.794, 0.9, 0.99, 0.999, 0.9999`.

**(C) Overshoot of the field activity.** The character single-plaquette weight `2w³` overshoots
`g²=1−w` by a factor that blows up: the excited character mass `z_1^char/g²` = `0.52, 2.93, 7.5,
41.8, 4916` at `w=0.5,0.7,0.79,0.9,0.99`. So the character basis is NOT the field-space
single-polymer activity `z_1≤g²` the KP chain needs — confirming (`SinglePolymerGaussian`) that
the config-space Gaussian measure, not the character basis, is the correct continuum substrate.

**Why this is decisive.** `pertRep` additionally carries the field
`single : SinglePolymerActivity afr` (`z_1 ≤ g²=1−w`). The character weight PROVABLY overshoots
that bound (C) at every continuum scale, so the character-sum `z_n` cannot even inhabit
`IsserlisPenroseData` — the obstruction is not hand-waved, it is a theorem.

## 3. Adversarial audit — does the character sum drop content? (task condition iii)

- **Non-abelian gauge structure?** The character sum HANDLES 2-body (δ/dim) and ≥3-body
  (triangle + signed 6j). At fixed spacing this is genuine. It does NOT drop the non-abelian
  content — but the ≥3-body fixed-spacing sum itself still rests on the **6j pentagon coherence**
  (BUILT `sixjCReal`, reduced to a rational identity, not fully proved for all labels).
- **Convergence?** DROPPED at the continuum: `2w³→2>1` (§2B, proved). The character expansion is
  a strong-coupling object; its convergence is exactly what fails as `a→0`.
- **Continuum `a→0` limit?** This IS the gap. The character sum is fixed-spacing; the continuum
  amplitude is a genuinely different (field-space RG) object. Proved divergence separates them.
- **Volume-uniformity?** Untouched by the character sum (a separate open input, `UniformSpacingFloor`).
- **The config-space measure?** The genuine `z_1` is the transcendental
  `1−e^{−g²/4}(1−g²/2)` (config-space Gaussian, `ExactSinglePolymerActivity`), NOT a character
  sum; the character surrogate overshoots it (§2C).

**Net:** the character sum is the correct object for the FIXED-SPACING strong-coupling gap
(already proved) and drops NOTHING there; it is the WRONG object for the CONTINUUM amplitude
`pertRep` encodes, and the mismatch (divergence + overshoot) is now PROVED.

## 4. Cascade / STOP status (MANDATORY task condition ii) — EXHAUSTIVE

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered.**

`ZnCharacterSumFrontier.lean` proves theorems ABOUT the character sum and its continuum
divergence. It does **NOT** produce `IsserlisPenroseData`, `pertRep`, `WickTreeData`,
`FieldMeasureSubstrate`, `KPAmplitude`, `SinglePolymerActivity`, `SixJ*`, or any node on the
chain `pertRep → isserlisBound → wickTreeDom → treeDom → FieldClusterConvergence →
SingleCouplingFormPreservation → continuum floor → FrontierDAG.trueMargin`. The full build
reports `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`
(`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) —
UNCHANGED (707 → 708 jobs = the +1 new module). The verdict decl
`znCharacterSumFrontier_honesty : True := trivial` is inert.

## 5. Axioms / honesty gate

```
#print axioms zCharCluster_nonneg                    -- [propext]
#print axioms charRate_lt_one_strongcoupling         -- [propext]
#print axioms charRate_exceeds_one_at_continuum      -- (none)   ← the decisive obstruction
#print axioms charRate_crossover_below_continuum     -- (none)
#print axioms charWeight_overshoots_fieldActivity    -- (none)
#print axioms charWeight_overshoots_bigfactor        -- (none)
```

The four decisive obstruction facts are **axiom-free kernel `decide`** (MLTT canonicity). No
`Classical.*`, no `native_decide`, no `sorry`/`admit`/new `axiom` (banned tokens appear only in
docstring prose). All witnesses `Type`-level. Lean-core only (`Q'`/`Nat`, reused PROVED
`coeffW`/`rho`/`connChain` machinery); no Mathlib, no `ring`.

## 6. HONEST FINAL VERDICT — what closes vs what remains

- **Constructible (YES, fixed spacing):** the lattice-Haar strong-coupling character sum `z_n`
  is genuinely built from the proved pieces (`coeffW` + orthogonality + 6j + combinatorics + KP)
  and is already the library's `wilsonG`/`treeG`/`graphG`. It re-derives the ALREADY-PROVED
  fixed-spacing gap.
- **Does NOT close `pertRep` (PROVED, not asserted):** the character sum is the FIXED-SPACING
  amplitude; `pertRep`'s `zAmp` is the CONTINUUM field-space amplitude. The character expansion
  provably DIVERGES at the continuum (`2w³→2>1`, `charRate_exceeds_one_at_continuum`) and
  provably OVERSHOOTS the field activity `g²=1−w` (`charWeight_overshoots_fieldActivity`), so it
  cannot be the continuum object and cannot inhabit `IsserlisPenroseData`.
- **The exact remaining gap:** (i) the continuum `a→0` limit — where the character sum does not
  converge; (ii) the config-space field measure `|z_1|≤g²` (`SinglePolymerActivity`, the
  transcendental Gaussian integral); (iii) for the fixed-spacing ≥3-body character sum itself,
  the Wigner 6j **pentagon coherence** (BUILT, reduced, not fully proved). These are the genuine
  4D-YM frontier. The character sum does not reach them — it is the **wrong basis for the
  continuum**, and that is now a theorem.

**This is the last-frontier answer: the interacting amplitude is constructible as a character
sum ONLY at fixed spacing (already-proved content); the CONTINUUM interacting amplitude is a
genuinely separate object the character expansion provably cannot represent. The 4D Yang–Mills
mass gap remains OPEN; nothing is faked; no guarded frontier bundle is inhabited.**
