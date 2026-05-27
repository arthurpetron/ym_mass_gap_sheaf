# LaTeX chapter split — one `.tex` file per logical code/Lean group

**Goal.** Make every Python and Lean logical group correspond to exactly
one `formal/*.tex` chapter (or appendix), so the written proofs are
tightly linked to the analytical and Lean code.  The umbrella
`formal/main.tex` (already in place) `\include`s these files in the
order documented in `docs/outline.md` §27.

Status legend:
- ✅ exists in `formal/`
- ⚙️ planned (file to be written)
- 🔁 exists but needs preamble strip + `\input`-ability before it can be
  pulled into `main.tex`

## Part I — Statement and roadmap

| Chapter file | Status | Maps to (code / Lean) |
|---|---|---|
| `abstract.tex` | ✅ | (front matter) |
| `introduction.tex` | ✅ | `computations/mass_gap_bound.py`, `lean/YMGap/MassGap/SU2.lean`, `lean/YMGap.lean` |
| `roadmap.tex` | ⚙️ Ch. 2 | (reading guide companion to introduction; cross-refs to all later chapters) |

## Part II — SU(2) representation-theory pilot

| Chapter file | Status | Maps to (code / Lean) |
|---|---|---|
| `su2-rep-theory.tex` | ⚙️ Ch. 3 | `computations/heat_kernel.py` (irrep data, Casimirs); `lean/YMGap/Sheaf/SU2KP.lean` (`Q'.C2_oneHalf`) |
| `heat-kernel-normalization.tex` | ⚙️ Ch. 4 | `computations/heat_kernel.py` (CANONICAL / WILSON conventions, `t = 2N/g²`); `notes/heat-kernel-normalization.md` |
| `buffer-shell.tex` | ⚙️ Ch. 5 | `computations/buffer_shell.py` (T6.1, T6.2 uniform-in-g bound); `lean/YMGap/BufferShell.lean`; `notes/single-plaquette-derivation.md` |
| `overlap-measure.tex` | ⚙️ Ch. 6 | `computations/overlap_measure.py` (`union_bound_overlap`, `standard_su2_trajectory`); `notes/union-bound-tightness.md` |
| `chaining-estimate.tex` | ⚙️ Ch. 7 | `computations/chaining_estimate.py` (T17.1, T17.2); `notes/chaining-estimate.md` |

## Part III — Sheaf framework and the inductive step

| Chapter file | Status | Maps to (code / Lean) |
|---|---|---|
| `sheaf-framework.tex` | 🔁 Ch. 8 | Definitions of `𝒜_k`, `𝒮_k`, the Grothendieck site (D2.1–D2.7); `lean/YMGap/Sheaf/*` |
| `inductive-state.tex` | 🔁 Ch. 9 | `computations/inductive_state.py`; `lean/YMGap/InductiveState.lean` |
| `block-spin-morphism.tex` | 🔁 Ch. 10 | Block-spin `T_b`; `lean/YMGap/Sheaf/PolymerDomination.lean` |
| `poly-atlas.tex` | ⚙️ Ch. 10b | `computations/poly_atlas.py` (if exists, else inline in inductive-state); `lean/YMGap/PolyAtlas.lean` |
| `moduli-algebra.tex` | ⚙️ Ch. 10c | `computations/moduli_vector.py`; `lean/YMGap/ModuliAlgebra.lean` |
| `small-field-kp.tex` | ⚙️ Ch. 11 | `computations/small_field_kp.py` (T8.1, c_λ Casimir-gap derivation); `lean/YMGap/Sheaf/SU2KP.lean` |
| `large-field-kp.tex` | ⚙️ Ch. 12 | `computations/large_field_kp.py` (T8.3, Brydges–Federbush K_lf derivation, μ_plaq audit); `notes/large-field-derivation.md` |
| `overlap-kp.tex` | ⚙️ Ch. 13 | `computations/overlap_kp.py` (T9.1, K_∩ ≤ K_sf + K_lf); Conjecture 7.4 |
| `sigma-hat-trajectory.tex` | ⚙️ Ch. 14 | `computations/sigma_hat_trajectory.py` (T10.1, T10.2, T10.3), `computations/chaining_eta_uplift.py` (T10.1-chain); `lean/YMGap/RG/SigmaHatPilot.lean`; `notes/sigma-hat-derivation.md` |
| `pilot-su2.tex` | ⚙️ Ch. 15 | `computations/pilot_su2.py` (the five-criterion validator, T11.1); `lean/YMGap/RG/InductiveStep.lean` |
| `mcmc-cross-check.tex` | ⚙️ Ch. 15b | `computations/su2_mcmc.py`, `computations/su2_mcmc_cross_check.py`; `notes/mcmc-cross-check.md` (if exists) |

## Part IV — Continuum limit and OS reconstruction

| Chapter file | Status | Maps to (code / Lean) |
|---|---|---|
| `uv-trajectory.tex` | ⚙️ Ch. 16 | `computations/uv_trajectory.py` (T12.1, T12.2); `computations/long_k_trajectory.py` (T12.5, K=10/20/50 decay) |
| `continuum-limit.tex` | ⚙️ Ch. 17 | `computations/continuum_limit.py` (T13.1, σ̂_∞ projective limit); `lean/YMGap/Continuum/*` |
| `continuum-measure.tex` | 🔁 Ch. 18 | The projective-limit μ_∞ construction (Milestone 7.2); `notes/continuum-limit.md` |
| `os-axioms.tex` | 🔁 Ch. 19 | OS axiom verification for μ_∞ (Milestone 8.1); `computations/os_axioms.py` if present; `notes/os-axiom-verification.md` |
| `os-reconstruction.tex` | 🔁 Ch. 20 | OS reconstruction quintuple, cluster-to-gap bridge (Milestone 8.2); `lean/YMGap/Continuum/OSReconstruction.lean` |

## Part V — The SU(2) mass-gap theorem

| Chapter file | Status | Maps to (code / Lean) |
|---|---|---|
| `mass-gap-theorem.tex` | 🔁 Ch. 21 | `computations/mass_gap_bound.py` (`derive_mass_gap_bound`); `lean/YMGap/MassGap/SU2.lean` (`mass_gap_SU2`); Milestone 9.1 |
| `mass-gap-discussion.tex` | ⚙️ Ch. 22 | Sharpness, Teper comparison, physical-unit calibration, SU(3) roadmap |

## Appendices

| Chapter file | Status | Maps to (code / Lean) |
|---|---|---|
| `appx-notation.tex` | ⚙️ App. A | (notation glossary; mirrors `docs/outline.md` §24) |
| `appx-lean-audit.tex` | ⚙️ App. B | `lean/AXIOM_AUDIT.md`; `scripts/lean_axiom_audit.py`; output of `make lean-audit` |
| `appx-lockstep.tex` | ⚙️ App. C | Python↔Lean lockstep test enumeration |
| `appx-fiducials.tex` | ⚙️ App. D | `computations/fiducial_sensitivity.py`, `m_0_tornado.py` (Fig. D.1), `m_0_bootstrap.py` (Fig. D.2); `notes/fiducials_notes.md` |
| `appx-refs-manifest.tex` | ⚙️ App. E | `docs/pdf_references/` manifest |
| `appx-roadmap.tex` | ⚙️ App. F | open obligations, SU(3) extension |

## Sequencing strategy

To finish the manuscript without thrashing:

1. **Drafting order**: roughly Part II → Part III → Part IV → Part V → Appendices.
   Each chapter file is self-contained (no preamble, no `\documentclass`)
   and can be `\include`d into `main.tex` immediately upon creation.
2. **Existing files (🔁)**: when a chapter file is touched for new content,
   strip its `\documentclass{article}` and per-file preamble in the same
   pass (the macros now live in `formal/preamble.tex`).  After the strip,
   uncomment its `\include` in `main.tex`.
3. **Cross-references**: every chapter ends with a **Code provenance**
   section listing the Python modules, test files, and Lean files
   relevant to it.  This is the bridge that fulfills the user's request
   for tight code↔proof linking.
4. **Lean signature panel**: each chapter's headline theorem carries
   a `Lean signature panel` infobox (using the class's
   `\begin{infobox}[title=Lean signature panel] ... \end{infobox}`)
   listing the Lean term name and its `#print axioms` output.

## Build conventions

- `make paper` (repo root) builds `formal/main.pdf` with
  `TEXINPUTS` pointing to `docs/arthur_tex_style/`.
- `scripts/install_arthur_tex_style.sh` installs the class globally
  (one-time, optional; preferred if the user wants to compile from
  outside `make`).
- `make figures` regenerates every SVG referenced in the figure registry.
- `make lean-audit` regenerates Appendix B from the live axiom-audit run.
