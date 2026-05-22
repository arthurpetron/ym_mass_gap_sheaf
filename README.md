# ym-mass-gap-sheaf

A constructive program for the $SU(2)$ Yang–Mills mass gap, organized around a sheaf-theoretic inductive step on the renormalization-group trajectory. The inductive state packages a presheaf $\mathcal{A}_k$ of bound-witnesses, a polymer-activity sheaf $\mathcal{S}_k$ with Kotecký–Preiss data, and a string-tension lower bound $\widehat{\sigma}_k$ that survives the block-spin pushforward up to a controlled 2-cell degradation.

See [`docs/context.md`](docs/context.md) for motivation, [`docs/outline.md`](docs/outline.md) for the technical specification, and [`work_plan.md`](work_plan.md) for the milestone schedule.

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

Phase 0 in progress; Milestone 0.1 (skeleton) is the current target. See `work_plan.md` for the up-to-date milestone status.
