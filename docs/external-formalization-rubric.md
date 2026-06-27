# External formalization rubric — YM mass gap & HEP math (2026-06-27)

Survey of external Lean/Coq formalizations of the Clay Yang–Mills statement and of
HEP mathematics, used as a **rubric** to (a) validate our own statement against the
canonical one and (b) honestly assess public "complete proof" claims. Pulled and
audited directly, not taken on description.

## 1. The canonical Lean *statement* — `lean-dojo/LeanMillenniumPrizeProblems`

Cloned; audited. **Sorry-free and user-axiom-free — because it is a STATEMENT, not a
proof.** The top-level target is a `Prop` that is never discharged:

```
def YangMillsExistenceAndMassGap (G) [CompactSimpleGaugeGroup G] : Prop :=
  ∃ (qft : QuantumYangMillsTheory G) (Δ : ℝ),
    ClayExistence qft ∧ HasMassGapSpectrum G qft Δ ∧ FiniteMassSpectrum G qft
```

Rubric-critical observations:
- **Bounded-Hamiltonian proxy.** `wightman.hamiltonian : LinearOperator H` is a *bounded*
  operator; the gap is `Disjoint (spectrum ℝ hamiltonian) (Set.Ioo 0 Δ)` via Mathlib's
  Banach-algebra `spectrum`. They state plainly: "We do not formalize the spectral theory
  of the Hamiltonian operator here." The true YM Hamiltonian is unbounded. So even the
  official statement uses the bounded-proxy shortcut.
- **Existence carried as unproven data.** `QuantumYangMillsTheory` bundles `WightmanAxioms`
  (self-adjoint positive H, vacuum, cyclicity, Poincaré), `ShortDistanceAgreement`,
  `StressEnergyTensor`, `OperatorProductExpansion`, `LocalOperatorAssignment` — all as
  `structure` fields. Nothing is constructed; the entire mathematical content is deferred
  into "does such a `qft` exist," which is the unproven `∃`.
- **Classical, Minkowski/Wightman.** `ℝ`, `InnerProductSpace`, `sSup`, `Dense`,
  `noncomputable`, Minkowski metric, Poincaré group. Not constructive.

This is the honest reference shape of the Clay target in a proof assistant: a precise
`Prop`, deliberately not proved.

## 2. `google-deepmind/formal-conjectures` #2365

An open call to formalize the YM conjecture. **No Lean code, no proof** — references the
Clay PDF and notes PhysLean as potential infrastructure. Confirms: no accepted Lean proof.

## 3. The publicized "complete proof" — `Shariq81/yang-mills-mass-gap` (Coq, not Lean)

The repo billed online as "the first complete machine-verified formalization of the
Yang-Mills mass gap theorem" (README badge: "Qed 1306"). Cloned and audited directly.

**It is not a complete proof of the Clay theorem, and its own documentation says so.**
- Incompleteness markers across the `.v` files (repo-wide grep):
  **48 `Admitted`, 83 `Axiom`, 75 `Hypothesis`, 142 `Parameter`, 18 `admit`, 1 `Conjecture`.**
  (Some `Parameter`s are legitimate, e.g. the gauge group; but `Admitted`/`admit` are
  literally unproven goals, and `Axiom`/`Hypothesis` assume content.)
- Their **own** `docs/WIGHTMAN_FRONTIER_STATUS.md` is honest and dispositive: the continuum
  reconstruction is "Reduced to ONE hypothesis (Balaban pointwise convergence)," with status
  "**PROVEN for YM₃ … OPEN for YM₄ (the core challenge)**," and "Wightman reconstruction
  (standard theorem, **not formalized**)." So the continuum/4D part — the actual Clay
  difficulty — is admitted-open, exactly as it should be.
- The lattice layer is "915 Qed, 17 Admitted." The "explicit gap" `m = β/10 − 4 for β > 50`
  is in **lattice units at fixed spacing** (and grows with β, which is a lattice artifact,
  not a finite physical continuum mass) — i.e. a fixed-spacing result, not the continuum gap.

Verdict: the README "complete" claim is an **overclaim**, contradicted by the repo's own
frontier doc. The genuine content is a fixed-spacing lattice gap plus a continuum *scaffold*
that bottoms out at an admitted Balaban-convergence hypothesis (`balaban_rg_scaffold.v`,
`yang_mills_weak_coupling_bridge.v`, `continuum_limit.v`). (The 327 KB
`zylphorian_yang_mills.v` is a further red flag of AI-generated bulk.)

Unrefereed PDF "proofs" (Medium, philarchive, academia.edu, arXiv 2506.00284 SU(3)) are in
the same category: claims without accepted verification. **No accepted proof of the Clay
problem exists.**

## 4. HEP mathematics — HepLean → PhysLean → Physlib

Real, serious, Mathlib-based, but **not** a YM-gap proof; it is HEP *math infrastructure*:
- **HepLean** (arXiv:2405.08863, Tooby-Smith): Lorentz group/algebra, Weyl fermions, real/
  complex Lorentz tensors, Pauli matrices, index notation (arXiv:2411.07667); physics
  results — anomaly cancellation conditions (triangle-diagram polynomial constraints), CKM
  matrices, Higgs potential.
- Renamed **PhysLean**, then merged with Lean-QuantumInfo into **Physlib** (general physics +
  quantum information). Reservoir: `@HEPLean/HepLean`, `@leanprover-community/Physlib`.
- Relevance to us: the *gauge-algebra / representation-theory* substrate (anomaly ACCs, Lie
  structure) is the natural external library for any group-theoretic inputs; it does **not**
  touch constructive QFT, OS reconstruction, lattice gauge theory, or the mass gap.

## 5. Rubric comparison — where THIS project stands

| Dimension | LeanMillennium (canonical) | Shariq81 (claimed "complete") | This project |
|---|---|---|---|
| Object | Clay `Prop`, unproven | Coq, lattice + continuum scaffold | constructive build + proved fixed-spacing gap |
| Hamiltonian | bounded proxy (Mathlib `spectrum`) | lattice transfer + bounded proxy | constructive located gap of real transfer op |
| Foundations | classical Mathlib, Minkowski/Wightman | classical Coq | **intuitionistic, Mathlib-free, Euclidean/OS** |
| Axiom budget | sorry-free (statement only) | **83 Axiom, 48 Admitted, 75 Hyp** | **only `propext` / `Quot.sound`** |
| Open content | the entire `∃` | continuum = admitted Balaban hyp (YM₄) | continuum = **precisely-named** obligations |
| Overclaim? | no (states it's a statement) | **yes** ("complete") | no — OPEN stated throughout |

Two takeaways that matter:
1. **Independent confirmation of our wall.** A separate serious effort, working in Coq,
   independently lands the continuum obstruction on **Balaban RG convergence for YM₄** — the
   same wall our R2/RG research map (`docs/continuum-closure-research-map.md`,
   `ContinuumClosureProgram.lean`) identified. The wall is real and correctly located.
2. **Our honesty posture is the differentiator.** Where the publicized repo overclaims
   "complete" while carrying 48 anonymous `Admitted` + 83 `Axiom`, we draw the *same*
   proved-vs-open line but (a) stay axiom-clean (`propext`/`Quot.sound` only), (b) name every
   open thing as a precise Type-level obligation, and (c) never label the continuum/Clay
   result closed. The canonical Lean repo agrees on the line; it just doesn't try to cross it.

The Clay problem remains **OPEN**. The rubric reinforces, rather than relaxes, that call.
