# Yang–Mills Mass Gap — Constructive Lean State & Path Forward (2026-07-02)

> **Status of the Clay problem: OPEN.** This document is an honest map of what is
> *proved unconditionally*, what is *proved modulo a named input*, and what remains
> *genuinely open*. Nothing here claims the 4D Yang–Mills mass gap.

## Headline (verified this snapshot)

| Metric | Value |
|---|---|
| `lake build` | **476/476 jobs green** |
| Modules (`YMGap/**/*.lean`) | 475 |
| Permitted axioms | `propext` (4669 gated decls) · `Quot.sound` (5) |
| Forbidden axioms (`Classical`/`sorryAx`/`native_decide`/`ofReduceBool`) | **0** |
| Code-position `sorry` | **0** (375 grep hits are all prose: "no `sorry`", "no `Classical`") |
| Head | `b1cfe0f`, `origin/main` |

Substrate: custom constructive reals `CReal` (Bishop regular sequences), no Mathlib,
MLTT/HoTT-valid (witnesses are Type-level data, not `Prop`-∃).

## Rubric

### Proved unconditional 🟩
- Fixed-spacing Clay target (gap + clustering + nontriviality + OS2 + ∞-volume mass).
- OS0/OS1 regularity; OS2 reflection positivity (diagonal, all orders/`t`).
- Complete GNS Hilbert space; transfer operator; vector-space + scalar ops on the completion.
- **Mass gap `Δ = −log sep > 0` for all `sep ∈ (0,1)`** (`mass_gap_hamiltonian_all`).
- **Spectrum-inf**: `Δ` is the located infimum of the excited spectrum (`spectrumInfResidual`, unconditional via the proved artanh monotonicities).
- **Operator-norm gap** `‖T|vac⊥‖ ≤ sep` (`diagResolution_normGap`); the mis-stated unbounded-`H` residual dissolved.
- **Spectral / effective-mass layer**: `C_O(t)=Σ|c_k|²λ_k^t`, long-time survival bound, lowest-state dominance, and the **effective-mass plateau `m_eff(t;a) → m_phys`** (`effectiveMass_convergesTo`, explicit `w⁵` second-gap modulus; `EffMassLogContinuity` closed).
- OS2 off-diagonal Gram positivity for the **explicit family M = 1…16** (`deMoivreNodeM1…16`); the DD/Markov side (`ddId`, sharp `(k+2)²` secant bound) fully proved.
- Reconstruction capstone `wilson_gns_reconstruction_gap` + `ReconstructionScorecardFinal` (six proved-unconditional fields).

### Proved modulo a named input 🟨
- **O(4) restoration** — fires with genuine content (invertible order-4 `rot4` automorphism; `betaDrop` *derived* from the reciprocal AF trajectory). Physics residual: one-loop `b₀>0`.
- **Coupling-uniform gap floor** — fires (dominant-mode surrogate). Genuine residual: `TrueMarginRecursion`, now *demoted* to a consequence of `UniformPhysicalCorrelationDecay`.
- **Physical Wilson form-gap** — fires on the character-diagonal model; physical `E_Λ` identification via the Haar bridge (see ③).
- **Loopy correlator** — real single-line decay proved outright; multi-component via the FP `≤` domination.

### Cited-classical 🟦
- σ-additive Minlos measure (Bochner–Minlos / nuclearity; cited OSforGFF `arXiv:2603.15770`, non-transferable to the constructive substrate). The mass gap does **not** depend on it (lives on the cylinder functional via clustering).

### Genuinely open 🟥 — the frontier

**Category-correct framing (do not conflate these):**
`mass gap ≠ rectangular Wilson-loop area law ≠ flux-tube`. The mass-gap open input is
**`UniformPhysicalCorrelationDecay`** (`∃ m₋>0, A<∞, ∀ a≪|x|≪L: |C_{a,L}(x)| ≤ A·e^{−m₋|x|}+ε(r)`),
proved to imply `MassGap ⇒ DownstreamFormalConsequences`. Confinement is the *separate*
`ScaleCovariantWilsonAreaLaw` (general loops); the rectangle is a *derived measurement lemma*.

| # | Core | Kind | Sharpest residual |
|---|---|---|---|
| ① | Fusion local-CLT (`FiniteSMargin`) | open-but-true, **irreducibly global** | theta-autoconvolution saddle margin; generic ρ-graded atom proved, but the all-`s` cancellation is transcendental (`L_even(1/4)≈1.987`) — Tate–Zelditch-depth |
| ② | Continuum `a→0` (`UniformPhysicalCorrelationDecay`) | open physics | spacing-uniform `m₋>0` + nonzero overlap `coeffSq₀>0` (Bałaban/SZZ class); reduction-mode complete |
| ③ | Wilson `E_Λ` / OS2-uniform (via `sin(kπ)=0`) | open-but-true (hybrid) | the arctan↔trig link `tanArctan` (formal identity `P=xQ` **proved**; residual = composed-series REC+VAL) **+** the CReal sine-addition law |
| ④ | Bounded `H=−log T` | mostly done | continuous-`f` Bernstein limit (norm-gap proved; off critical path) |
| ⑤ | Minlos σ-additive lift | classical boundary | cited, firewalled — not needed for the gap |

## What advanced this session

- **Correlation-decay recast** (② category-correction): mass gap ⇒ `UniformPhysicalCorrelationDecay`; `TrueMarginRecursion` and the rectangular Wilson loop both demoted; confinement separated.
- **Spectral / effective-mass layer**: the operational diagnostic `m_eff → m_phys` made a proved theorem with an explicit modulus.
- **Cores ③④① in parallel**: ④ dissolved to the norm-gap; ③ reduced to the arctan↔trig atom; ① sharpened (generic ρ-graded Hankel atom) and *confirmed irreducibly global*.
- **The shared π-trig primitive** (`cosC/sinC : CReal → CReal`), range-extended (`cosFullC/sinFullC`), closing OS2 for M ≤ 16 and reducing both ③ and OS2-uniform to `sin(kπ)=0`.
- **The Machin `ℤ[i]` combinatorics DECIDED axiom-free** (`e^{iπ}=−1` as integer arithmetic), isolating `sin(π)=0` to the arctan↔trig atom, whose **formal coefficient identity `P=xQ` is now proved** (`odeShift`).
- Two honest evidence/interface bridges (`ObservedMassGap`, the codynamic `ConstructiveShell`), instantiated from proved objects.

## Method notes (what worked)

- **The epistemic-type router** (build tool / constructivize-known / reduce-and-cite / decide-boundary) correctly predicted which cores would yield; its self-corrections (④'s "bounded-away-from-0" was wrong; ①'s "one margin number" was too optimistic; ③ is a hybrid) were themselves productive.
- **Lakatos discipline**: machine-refuting dead routes (summand-wise reserve, odd-`M` `UnitRootPair`, the loopy `.eqv` bridge, the false product-functional identity) is the highest-value behavior — each refutation forbade a method class and sharpened the true theorem.
- **Decide-the-arithmetic, isolate-the-transcendental**: the Machin identity collapsing to `decide` is the template — push combinatorial content into decidable arithmetic, leaving a single named analytic atom.

## Path forward (prioritized)

1. **④ Bernstein limit** — clean, near-done retirement of a core (continuous-`f` functional calculus on the located spectrum).
2. **③ composition-of-series** — the REC+VAL residual under `tanArctan`: constructive composition of convergent power series + convergence moduli (a real multi-step build; unlocks ③ + OS2-uniform via `sin(kπ)=0`). Companion: lift `TrigAdd`'s `Q'`-angle law to the signed CReal-angle sine-addition law (repo-open).
3. **① discrete-Laplace / Tate–Zelditch** — the deep continuum crux; a global saddle bound carrying the window profile (genuine research; expect sharpening).
4. **② / ⑤** — leave as sharp, cited, named boundaries (open physics; classical). Reduction mode complete.

*The fixed-spacing and reconstruction halves are machine-checked and unconditional; the
continuum reduces to the five named cores above. The Clay Yang–Mills mass-gap problem
remains open, and every open input is an explicit, uninhabited, honestly-named object.*
