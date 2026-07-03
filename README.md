# ym-mass-gap-sheaf

A constructive program for the **Yang–Mills existence and mass gap** problem (Clay Millennium Problem), organized around a sheaf-theoretic inductive step on the renormalization-group trajectory. The inductive state packages a presheaf $\mathcal{A}_k$ of bound-witnesses, a polymer-activity sheaf $\mathcal{S}_k$ with Kotecký–Preiss data, and a string-tension lower bound $\widehat{\sigma}_k$ that survives the block-spin pushforward up to a controlled 2-cell degradation.

## The goal (Clay problem statement)

Per Jaffe–Witten, the prize requires proving that **for *any* compact simple gauge group $G$, a non-trivial quantum Yang–Mills theory exists on $\mathbb{R}^4$ and has a mass gap $\Delta > 0$**, where "exists" means establishing axioms at least as strong as Osterwalder–Schrader / Wightman. Concretely, three requirements:

- **(R1) All compact simple $G$.** The classification is *finite*: the families $A_n, B_n, C_n, D_n$ plus the five exceptionals $G_2, F_4, E_6, E_7, E_8$. **Enumerating groups one at a time (SU(2), SU(3), SU(4), …) is *not* a path** — the group dependence must be discharged by a single *uniform / worst-case* argument. Our strategy: every budget channel is monotone in the two invariants $h^\vee$ (dual Coxeter number) and $\Delta$ (smallest nonzero Casimir gap), both globally minimized **only at $A_1 = \mathrm{SU}(2)$** ($h^\vee = 2$, $\Delta = 3/4$). So *all groups* follow from one monotonicity lemma + the SU(2) closure. This reduction is assembled and axiom-clean in Lean (`MassGap/SimpleGroup.lean`, `mass_gap_simple_group_of_osReconstruction`); SU(N) instances are corollaries, not new theorems.
- **(R2) Continuum existence on $\mathbb{R}^4$.** A non-trivial (non-Gaussian) continuum measure / Wightman theory via OS reconstruction (OS0–OS4 + the GNS/completion lift). **This is the dominant open frontier**, currently carried as a named interface. The gap is *not* obtained via Stone's theorem / the unbounded self-adjoint spectral theorem (that route is obstructed for general bounded operators constructively); it is the **located second eigenvalue of the compact finite transfer operator** (`Continuum/LocatedSpectralGap.lean`; `sep = w³ < 1`, `Δ = −log sep`, proved unconditional at fixed spacing). The genuinely open continuum content is the *spacing-uniform* survival of that gap as $a\to0$ (`Continuum/UniformCorrelationDecay.lean`, `UniformPhysicalCorrelationDecay`) — a correlation-decay statement, not a spectral-theorem lift. (Note: the bounded continuous functional calculus $f(T)$ was subsequently *retired* — `Continuum/WilsonFCHead.lean` — so R2 is now purely the $a\to0$ physics.)
- **(R3) Mass gap $\Delta_G > 0$.** A quantitative, constructive lower bound on the Hamiltonian spectrum above the vacuum — routed through the renormalized string tension $\widehat\sigma_\infty > 0$, the cluster$\leftrightarrow$gap bridge (proven at finite volume), and the $\sqrt{}$-bridge $m_0 \ge \sqrt{\widehat\sigma_\infty}$.

See [`docs/context.md`](docs/context.md) for motivation, [`docs/outline.md`](docs/outline.md) for the technical specification, [`docs/uniform-parametric-bound-plan.md`](docs/uniform-parametric-bound-plan.md) for the worst-case-reduction strategy (R1), and [`work_plan.md`](work_plan.md) for the milestone schedule.

## Setup

Python 3.11+ with `pip` and a virtual environment:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
```

A working LaTeX installation with `latexmk` is required for `make paper`.

## Common tasks

| Command         | What it does                                              |
| --------------- | --------------------------------------------------------- |
| `make test`     | Run the `pytest` suite.                                   |
| `make lint`     | Run `ruff check` and `mypy` (strict, 100% type coverage). |
| `make figures`  | Regenerate plots in `visualizations/` (Phase 1+).         |
| `make paper`    | Build `formal/main.tex` to PDF via `latexmk`.             |
| `make clean`    | Remove Python, type-checker, and LaTeX build artifacts.   |

## Layout

| Path               | Role                                                                    |
| ------------------ | ----------------------------------------------------------------------- |
| `docs/`            | Authoritative specification (`outline.md`) and motivation (`context.md`). |
| `work_plan.md`     | Milestone schedule. The "current task" is its lowest open milestone.    |
| `computations/`    | Python implementations. Every module has a paired note and test.        |
| `tests/`           | `pytest` suite, one `test_<module>.py` per `computations/<module>.py`.  |
| `notes/`           | Prose derivations paired with `computations/` modules.                  |
| `formal/`          | LaTeX paper sources.                                                    |
| `visualizations/`  | Paper figures (`structure/`), pilot plots (`pilot/`), and more.         |
| `lean/`            | Lean 4 formalization of the constructive steps.                         |

## Constructive law

Every existence claim in code returns an explicit witness — no function may return `True` or `1` as a "proof"; it must return the witnessing object (the bound, the modulus, the KP pair). See `work_plan.md` § Cross-cutting policies, and `lean/AGENTS.md` for the Lean-side enforcement.

## Status

The **group dependence (R1) is structurally closed**: the worst-case reduction to SU(2) is assembled and axiom-clean in Lean (`mass_gap_simple_group_of_osReconstruction`), modulo one named analytic input — the uniform character-tail domination $Z_t(G) \le Z_t(\mathrm{SU}(2))$ (discharged via the gap floor $\Delta \ge 3/4$ + a rank-collapsing majorant, *not* per-group). SU(2) closes unconditionally at $\sigmâ$-budget + finite-volume-gap parity; SU(3)/SU(N) are corollaries.

The **continuum existence (R2) is the open frontier**: OS reconstruction and the continuum spectral lift remain paper-level interfaces. This — not more groups — is what stands between the current state and the prize.

See `work_plan.md` and `docs/uniform-parametric-bound-plan.md` for the up-to-date status.
