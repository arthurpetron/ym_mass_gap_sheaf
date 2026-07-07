# Structural adjudication of the `singleStep` 3-piece decomposition

**Date:** 2026-07-07.
**Question (from `docs/PROGRESS-LEDGER.md`):** is `singleStep ⇐ uniform_in_m ∧
channel_feedback ∧ real_defect_identification` a REAL 3-piece reduction (each piece
strictly weaker, `F = 3`), or FAKE (channel_feedback and/or identification logically
EQUAL to `singleStep`, so `F ≈ 1`)?

**Deliverable:** `lean/YMGap/Continuum/SingleStepDecompositionAdjudication.lean`
(new, imported in `YMGap.lean`). NOT another `:= SingleStepDefectBound` alias — it
carries the equivalence/independence PROOFS.

---

## VERDICT (machine-checked)

**The decomposition is FAKE. `F` is NOT 3; it is ≈ 1: an ATOMIC core `singleStep`
(= channel_feedback = real_defect_identification) plus one strictly-weaker,
independent, NON-core-shrinking evidence lemma `uniform_in_m`.**

The content of the `singleStep` field, isolated as a standalone predicate on the
fixed data `(afr, tm)`, is

    SingleStepProp afr tm  :=  ∀ k, (1 − afDefectSeq afr k) · tm k ≤ tm (k+1).

| Piece | Precise content | (A) piece→singleStep | (B) singleStep→piece | Verdict |
|---|---|---|---|---|
| `channel_feedback` | the `s≥2 → s=1` next-scale transfer = the per-step recursion | `id` | `id` | **DEFINITIONAL ALIAS** (`Iff.rfl`) |
| `real_defect_identification` | `∃ realδ` governing the margin with `realδ ≤ afDefectSeq` | PROVED (needs `tm ≥ 0`) | PROVED (take `realδ := afDefectSeq`) | **ALIAS** (bi-implication) |
| `uniform_in_m` | `Cdef_m ≤ 6(1−w)²` — a fusion/`afr`-only bound, no `tm` | — | — | **strictly weaker + independent; NOT core-shrinking** |

### 1. `channel_feedback` — DEFINITIONAL ALIAS

The honest per-step propositional content of "the higher-channel (`s ≥ 2`) fused
remainder feeds the next scale's fundamental (`s = 1`) gap over the recursion" IS
that per-step recursion inequality — there is no separable single-scale sub-statement
to isolate (contrast `uniform_in_m`, which genuinely is a distinct single-scale
object `Cdef_m`). Formalized as `ChannelFeedback afr tm`, it is **defeq** to
`SingleStepProp afr tm`:

- `channelFeedback_iff_singleStep : ChannelFeedback afr tm ↔ SingleStepProp afr tm := Iff.rfl`
- both `channelFeedback_of_singleStep` and `singleStep_of_channelFeedback` are the
  identity map.

It carries **no content distinct from `singleStep`**. This is a fake decomposition
node — consistent with the MK/Birkhoff docs' "verbatim singleStep", now proved.

### 2. `real_defect_identification` — LOGICALLY EQUAL (bi-implication)

`RealDefectIdentification afr tm` (`Type`, `Σ'`) bundles a real per-step defect
`realδ` with (a) `real_step : (1 − realδ_k)·tm_k ≤ tm_{k+1}` and (b)
`identified : realδ_k ≤ afDefectSeq afr k` (the "real 4D block-spin defect = the
fusion object" identification, as data). BOTH directions are PROVED:

- **(A) `singleStep_of_realDefectIdentification`** (needs `tm ≥ 0`, which holds
  physically — the margin is a mass/spacing ratio): from `realδ_k ≤ δ_model_k`,
  `(1 − δ_model_k) ≤ (1 − realδ_k)`, so
  `(1 − δ_model_k)·tm_k ≤ (1 − realδ_k)·tm_k ≤ tm_{k+1}`.
- **(B) `realDefectIdentification_of_singleStep`**: take `realδ := afDefectSeq afr`.
  The "identification" adds NOTHING — the model defect is itself a legal witness, and
  the `real_step` field is then verbatim `singleStep`.

Both directions ⟹ equi-inhabited on the physical domain ⟹ **ALIAS**, not strictly
weaker.

### 3. `uniform_in_m` — independent, strictly weaker, NOT core-shrinking

`uniform_in_m` (`Cdef_m ≤ 6(1−w)²`, and every fusion/model-side single-scale bound)
is a proposition in the `afr`/fusion data ALONE — it never mentions the free function
`tm`. `singleStep`'s truth VARIES with `tm` at FIXED `afr`, machine-checked:

- `singleStep_satisfiable_zero`: holds for `tm ≡ 0` (`(1−δ_k)·0 ≤ 0`);
- `singleStep_falsifiable`: FAILS for the concrete `tm = (1,0,0,…)` — at `k=0`,
  `(1−δ_0)·1 ≤ 0` would force `1−δ_0 ≤ 0`, but `δ_0 = afDefectSeq afr 0 ≤ 1/2`
  (`renDefect_le_half`), so `1−δ_0 ≥ 1/2 > 0`, contradiction.

Since `singleStep` is a non-trivial function of `tm` at fixed `afr`, **no `afr`-only
statement can imply or be equivalent to `singleStep`.** Independently, `docs/uniform-m
-2026-07-07.md` §5 already argues (prose) that even a fully-proved `uniform_in_m`
does not inhabit `singleStep` (no true-margin construction; channel feedback; different
functional). So `uniform_in_m` is a strictly-weaker EVIDENCE lemma whose discharge
does not shrink the `singleStep` core — not a genuine core-shrinking `F`-node.

### 4. The over-count, machine-checked

- `decomposition_collapses_to_singleStep`: the 3-piece conjunction implies
  `singleStep` using ONLY `real_defect_identification` — the `_uniform : True`
  conjunct is DISCARDED (unused). The claimed `singleStep ⇐ uniform ∧ channel ∧
  identification` is really `singleStep ⇐ (identification = singleStep)`.
- `channel_alone_gives_singleStep`: a SINGLE alias conjunct (`channel_feedback`)
  already suffices. The conjunction is padded.
- `adjudication_verdict`: bundles (1) the channel `Iff`, (2) the identification
  implication, (3) the satisfiable+falsifiable pair — the whole verdict in one
  axiom-clean theorem.

---

## HONEST `F` count and the consequence for the solve path

**`F ≈ 1`, not 3.** `channel_feedback` and `real_defect_identification` are the SAME
obligation as `singleStep`; only `uniform_in_m` is a distinct statement, and it is
strictly weaker + independent + non-core-shrinking. The prior ledger over-counted `F`
by treating two aliases as separate frontier nodes. The confirmation-loop counter `C`
(currently 14) and this adjudication together confirm: the last ~20 rounds re-derived
`singleStep` under new names; the "decomposition" (status-2) did not produce three
independent strictly-weaker pieces.

**`singleStep` is ATOMIC beyond `uniform_in_m`.** Closing `uniform_in_m` (the fusion
`Cdef_m ≤ 6(1−w)²`, which reduces to the existing open local-CLT core
`FusionConvLogConcaveCore`) is a genuine partial result and honest evidence, but it
does NOT shrink the hard core. The remaining core is the irreducible continuum
non-perturbative obligation: the construction of the true dimensionless-margin
sequence `trueMargin_k = m_lat(a_k)/a_k` together with its real per-step recursion
`(1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}` over the full RG flow.

**The only honest attacks left on the hard core:**
- (a) prove the atomic `singleStep` DIRECTLY (the true-margin construction + its
  real per-step recursion — the non-perturbative continuum input); OR
- (b) find a genuinely-NEW strictly-weaker reduction. **None is known.** Every
  "decomposition" move so far (MK free-energy variational, Birkhoff/Hilbert-metric,
  uniform-in-m parallel fusion, RG-flow assembly, multiscale polymer) reduces TO
  `singleStep`, not below it. There is no further "decomposition" move that produces
  independent strictly-weaker pieces; the next step is (a).

There is NO gatekeeping consequence: the residual `singleStep` is the live target.
The adjudication redirects effort away from the two phantom `F`-nodes (which would be
pure `C`-loop re-derivations) and onto (a) — the atomic real per-step recursion.

---

## Build / gate status

- `lake build` **GREEN** (744 jobs, exit 0).
- `YMGapGuard` **GREEN**: "frontier-guard OK: 5 Clay-frontier types unconditionally
  uninhabited across YMGap.*". This module inhabits NONE of the 5 guarded types and
  does NOT inhabit `SingleStepDefectBound` (it adjudicates the structure; every
  producer is an open binder or a refutation).
- `#print axioms` on all 11 load-bearing declarations: `propext` / `Quot.sound` only.
  No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`, no `ring`.
- **No new `:= SingleStepDefectBound` alias emitted** — `C` does NOT increment. The
  deliverable is the structural verdict (equivalence proofs + independence
  certificate), not another confirmation.

## Recommended ledger edits (for the human)

- `F`: 3 → **1** (drop `channel_feedback` and `real_defect_identification` as
  separate frontier nodes — they are `singleStep`; keep `uniform_in_m` reclassified
  as a strictly-weaker EVIDENCE lemma, not a core-shrinking obligation).
- `singleStep` status ladder: step 2 ("DECOMPOSED into 3 strictly-weaker pieces") is
  **refuted** — the decomposition was fake. `singleStep` is atomic beyond
  `uniform_in_m`; the honest status is "1 (numerically verified true), core atomic".
- Anti-loop rule: attacks on `channel_feedback` / `real_defect_identification` are
  now PROVABLY loops (they are `singleStep`); only (a) direct atomic attack or (b) a
  genuinely-new reduction is non-loop.
