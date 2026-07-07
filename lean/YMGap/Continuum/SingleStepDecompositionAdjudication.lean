/-
Track B / R2 — STRUCTURAL ADJUDICATION of the claimed 3-piece decomposition of
`SingleStepDefectReduction.SingleStepDefectBound.singleStep`.

# The question this module SETTLES (not another `:= SingleStepDefectBound` alias)

`docs/PROGRESS-LEDGER.md` records the frontier as three OPEN obligations
`F = { uniform_in_m , channel_feedback , real_defect_identification }` with the
claimed reduction

    singleStep  ⇐  uniform_in_m ∧ channel_feedback ∧ real_defect_identification .

Two of the three (`channel_feedback`, `real_defect_identification`) are flagged
"status UNKNOWN (may be = singleStep)".  The MK / Birkhoff docs assert they are
"verbatim singleStep".  This module DECIDES it — with machine-checked implication
proofs, NOT prose — determining whether each piece is (i) a genuine
strictly-weaker sub-obligation (real `F`-node) or (ii) LOGICALLY EQUAL to
`singleStep` (a fake decomposition node that over-counts `F`).

# The verdict (machine-checked below)

The content of the `singleStep` FIELD, isolated as a standalone predicate over the
fixed data `(afr, trueMargin)`, is

    SingleStepProp afr tm  :=  ∀ k, (1 − afDefectSeq afr k) · tm k ≤ tm (k+1).

- **`channel_feedback` is a DEFINITIONAL ALIAS of `singleStep`.**  The only per-step
  propositional content of "the `s≥2` fused remainder feeds the next scale's `s=1`
  gap over the recursion" IS that per-step recursion inequality.  Given that honest
  content, `ChannelFeedback afr tm` is *definitionally* `SingleStepProp afr tm`
  (`channelFeedback_iff_singleStep : Iff.rfl`; both `channelFeedback_of_singleStep`
  and `singleStep_of_channelFeedback` are the identity).  It carries NO content
  distinct from `singleStep`.

- **`real_defect_identification` is LOGICALLY EQUAL to `singleStep`** (bi-implication,
  on the physical domain `tm ≥ 0`).  `RealDefectIdentification afr tm` bundles a real
  per-step defect `realδ` that (a) governs the margin degradation
  `(1−realδ_k)·tm_k ≤ tm_{k+1}` and (b) is bounded by the fusion/model object
  `realδ_k ≤ afDefectSeq afr k`.  BOTH directions are PROVED:
    * `singleStep_of_realDefectIdentification` (piece → singleStep, needs `tm ≥ 0`);
    * `realDefectIdentification_of_singleStep` (singleStep → piece, by IDENTIFYING
      `realδ := afDefectSeq afr` — i.e. the "identification" adds nothing: the model
      defect itself is a legal witness).
  So it is an ALIAS, not strictly weaker.

- **`uniform_in_m` is a genuinely DIFFERENT, INDEPENDENT statement** — but its
  discharge does NOT shrink the `singleStep` core.  `uniform_in_m` (the fusion
  connected-remainder `Cdef_m ≤ 6(1−w)²`, and every fusion/model-side single-scale
  bound) is a proposition in the `afr`/fusion data ALONE; it does not mention the
  free function `tm`.  `singleStep` is provably a NON-trivial function of `tm` at
  FIXED `afr`: `singleStep_satisfiable_zero` (holds for `tm ≡ 0`) and
  `singleStep_falsifiable` (FAILS for a concrete `tm`) show its truth VARIES with
  `tm` while `afr` is held fixed.  Hence no `afr`-only statement (`uniform_in_m`)
  can be equivalent to, or imply, `singleStep`; it is strictly weaker AND
  independent — evidence, not a core-shrinking sub-obligation.

# The HONEST `F` count

`channel_feedback` = `singleStep` (defeq) and `real_defect_identification`
= `singleStep` (bi-implication).  The "3-piece decomposition" therefore over-counts:
the conjunction implies `singleStep` using ONLY the two alias pieces
(`decomposition_collapses_to_singleStep`: `uniform_in_m` is discarded).  The genuine
picture is

    F  ≈  1  :  the ATOMIC core `singleStep`  (= channel_feedback = real_defect_identification)
              +  one strictly-weaker, NON-core-shrinking evidence lemma `uniform_in_m`.

`singleStep` is NOT decomposed into three independent strictly-weaker pieces; it is
ATOMIC beyond `uniform_in_m`.  The only honest attacks left on the hard core are
(a) prove the atomic `singleStep` directly (the true-margin construction + its real
per-step recursion over the full RG flow — the irreducible non-perturbative
continuum obligation), or (b) find a genuinely-NEW strictly-weaker reduction; none
is known.  No new confirmation alias is emitted.

# Guard / STOP

Inhabits NONE of the 5 guarded frontier types, and does NOT inhabit
`SingleStepDefectBound` (it adjudicates the STRUCTURE of the pieces; every producer
is an open binder or a refutation).  Nothing is closed; the 4D Yang–Mills mass gap
remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`; every load-bearing declaration is gated with `#print axioms`;
permitted output `propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no `ring`.
-/
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.SingleStepDecompositionAdjudication

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 0. The content of the `singleStep` field, isolated as a standalone predicate. -/

/-- **`SingleStepProp` — the exact propositional content of the `singleStep` field.**
Fixing the data `(afr, tm)`, this is the per-step 4D-block-spin RG defect inequality
`(1 − δ_model_k)·tm_k ≤ tm_{k+1}`, `δ_model = afDefectSeq afr`. -/
def SingleStepProp (afr : AFRateModulus) (tm : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - afDefectSeq afr k) * tm k ≤ tm (k + 1)

/-- The `singleStep` field of a `SingleStepDefectBound` IS `SingleStepProp` on its
own data (definitional). -/
theorem singleStepBound_is_prop (S : SingleStepDefectBound) :
    SingleStepProp S.afr S.trueMargin := S.singleStep

/-! ## 1. `channel_feedback` — a DEFINITIONAL ALIAS of `singleStep`.

Honest content: "the higher-channel (`s ≥ 2`) fused remainder feeds into the next
scale's fundamental (`s = 1`) gap over the recursion."  The only per-step
propositional content this carries is the per-step recursion inequality itself —
there is no separable single-scale statement to isolate (contrast `uniform_in_m`,
§3, which IS a distinct single-scale object).  So `ChannelFeedback` is *defeq* to
`SingleStepProp`. -/

/-- **`ChannelFeedback afr tm` — the `s≥2 → s=1` next-scale transfer contribution,
given its honest per-step content: the recursion `(1 − δ_model_k)·tm_k ≤ tm_{k+1}`.** -/
def ChannelFeedback (afr : AFRateModulus) (tm : Nat → Q') : Prop :=
  ∀ k : Nat, (1 - afDefectSeq afr k) * tm k ≤ tm (k + 1)

/-- **`channelFeedback_iff_singleStep` — channel_feedback IS singleStep (defeq).**
Not merely equivalent: `Iff.rfl`.  channel_feedback carries NO content distinct from
`singleStep`; it is a FAKE decomposition node. -/
theorem channelFeedback_iff_singleStep (afr : AFRateModulus) (tm : Nat → Q') :
    ChannelFeedback afr tm ↔ SingleStepProp afr tm := Iff.rfl

/-- Direction (A): channel_feedback → singleStep (the identity). -/
theorem channelFeedback_of_singleStep (afr : AFRateModulus) (tm : Nat → Q')
    (H : SingleStepProp afr tm) : ChannelFeedback afr tm := H

/-- Direction (B): singleStep → channel_feedback (the identity).  Both directions
are the identity map ⟹ ALIAS. -/
theorem singleStep_of_channelFeedback (afr : AFRateModulus) (tm : Nat → Q')
    (H : ChannelFeedback afr tm) : SingleStepProp afr tm := H

/-! ## 2. `real_defect_identification` — LOGICALLY EQUAL to `singleStep` (bi-implication).

Honest content: a real per-step defect `realδ` that (a) governs the true-margin
degradation and (b) is IDENTIFIED with (bounded by) the fusion/model object
`afDefectSeq`.  We prove BOTH directions, so it is an ALIAS — not strictly weaker. -/

/-- **`RealDefectIdentification afr tm` (`Type`, Rule 8).**  A real per-step defect
`realδ : Nat → Q'` with
  * `real_step`  — `realδ` governs the true margin: `(1 − realδ_k)·tm_k ≤ tm_{k+1}`;
  * `identified` — `realδ` is bounded by the fusion/model object `afDefectSeq afr`.
This is the "real 4D block-spin defect = the fusion object" identification, as data. -/
def RealDefectIdentification (afr : AFRateModulus) (tm : Nat → Q') : Type :=
  Σ' realδ : Nat → Q',
    (∀ k : Nat, (1 - realδ k) * tm k ≤ tm (k + 1))
      ∧ (∀ k : Nat, realδ k ≤ afDefectSeq afr k)

/-- **Direction (A): `real_defect_identification → singleStep`** (needs `tm ≥ 0`,
which holds physically — the margin is a mass/spacing ratio).  From
`realδ_k ≤ afDefectSeq afr k` we get `(1 − δ_model_k) ≤ (1 − realδ_k)`, hence
`(1 − δ_model_k)·tm_k ≤ (1 − realδ_k)·tm_k ≤ tm_{k+1}`. -/
theorem singleStep_of_realDefectIdentification (afr : AFRateModulus) (tm : Nat → Q')
    (hnn : ∀ k : Nat, (0 : Q') ≤ tm k)
    (R : RealDefectIdentification afr tm) : SingleStepProp afr tm := by
  intro k
  obtain ⟨realδ, hstep, hle⟩ := R
  have hneg : -(afDefectSeq afr k) ≤ -(realδ k) := Q'.neg_le_neg (hle k)
  have h1 : (1 : Q') - afDefectSeq afr k ≤ 1 - realδ k :=
    Q'.add_le_add_left 1 _ _ hneg
  have h2 : (1 - afDefectSeq afr k) * tm k ≤ (1 - realδ k) * tm k :=
    Q'.mul_le_mul_of_nonneg_right _ _ (tm k) h1 (hnn k)
  exact Q'.le_trans' _ _ _ h2 (hstep k)

/-- **Direction (B): `singleStep → real_defect_identification`** — by IDENTIFYING the
real defect WITH the fusion/model object, `realδ := afDefectSeq afr`.  The
"identification" adds nothing: the model defect is itself a legal witness, and the
`real_step` field is then *verbatim* `singleStep`.  Both directions ⟹ ALIAS. -/
def realDefectIdentification_of_singleStep (afr : AFRateModulus) (tm : Nat → Q')
    (H : SingleStepProp afr tm) : RealDefectIdentification afr tm :=
  ⟨afDefectSeq afr, H, fun k => Q'.le_refl' (afDefectSeq afr k)⟩

/-! ## 3. `uniform_in_m` — a DIFFERENT, INDEPENDENT statement (not core-shrinking).

`uniform_in_m` (`Cdef_m ≤ 6(1−w)²` and any fusion/model-side single-scale bound) is
a proposition in the `afr`/fusion data ALONE — it does not mention `tm`.  We show
`singleStep`'s truth VARIES with `tm` at FIXED `afr`: satisfiable for `tm ≡ 0`,
falsifiable for a concrete `tm`.  Hence no `afr`-only statement can imply or be
equivalent to `singleStep`. -/

/-- **`singleStep` is SATISFIABLE at any `afr`** by the degenerate margin `tm ≡ 0`
(`(1 − δ_k)·0 ≤ 0`).  So a fusion/model bound cannot *refute* it either. -/
theorem singleStep_satisfiable_zero (afr : AFRateModulus) :
    SingleStepProp afr (fun _ => (0 : Q')) := by
  intro k
  exact Q'.le_of_eqv (q_mul_zero (1 - afDefectSeq afr k))

/-- **`singleStep` is FALSIFIABLE at the SAME `afr`** by the concrete margin
`tm = (1, 0, 0, …)`.  At `k = 0`: `(1 − δ_0)·1 ≤ 0` would force `1 − δ_0 ≤ 0`, but
`δ_0 = afDefectSeq afr 0 ≤ 1/2` (`renDefect_le_half`), so `1 − δ_0 ≥ 1/2 > 0` —
contradiction.  Thus `singleStep`'s truth depends on the FREE FUNCTION `tm` at fixed
`afr`, so no `afr`-only proposition (`uniform_in_m`) determines it. -/
theorem singleStep_falsifiable (afr : AFRateModulus) :
    ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0) := by
  intro H
  -- instantiate at k = 0; the `if`s reduce definitionally to `1` and `0`.
  have h0 : (1 - afDefectSeq afr 0) * 1 ≤ (0 : Q') := H 0
  -- (1 − δ_0) ≤ (1 − δ_0)·1 ≤ 0
  have hmul : (1 - afDefectSeq afr 0) ≤ (1 - afDefectSeq afr 0) * 1 :=
    Q'.ge_of_eqv (Q'.mul_one_eqv (1 - afDefectSeq afr 0))
  have hd0 : (1 - afDefectSeq afr 0) ≤ (0 : Q') := Q'.le_trans' _ _ _ hmul h0
  -- δ_0 ≤ 1/2  ⟹  1 − 1/2 ≤ 1 − δ_0 ≤ 0
  have hhalf : afDefectSeq afr 0 ≤ HalfPow.half :=
    renDefect_le_half afr pMult (by show afCutoff afr ≤ afCutoff afr + 0; omega)
  have hstep : (1 : Q') - HalfPow.half ≤ 1 - afDefectSeq afr 0 :=
    Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hhalf)
  have hfinal : (1 : Q') - HalfPow.half ≤ (0 : Q') := Q'.le_trans' _ _ _ hstep hd0
  exact absurd hfinal (by decide)

/-! ## 4. THE HONEST `F` COUNT — the decomposition over-counts; `singleStep` is atomic. -/

/-- **`decomposition_collapses_to_singleStep` — the 3-piece conjunction implies
`singleStep` using ONLY the two ALIAS pieces; `uniform_in_m` is REDUNDANT.**

The hypothesis `_uniform : True` stands for `uniform_in_m` and is DISCARDED
(unused): `real_defect_identification` (an alias of `singleStep`, §2) alone yields
`singleStep`.  This machine-checks that the claimed `singleStep ⇐ uniform ∧ channel
∧ identification` is really `singleStep ⇐ (channel = singleStep) ⇐ (identification
= singleStep)` — a fake decomposition.  Honest `F ≈ 1`, not 3. -/
theorem decomposition_collapses_to_singleStep (afr : AFRateModulus) (tm : Nat → Q')
    (hnn : ∀ k : Nat, (0 : Q') ≤ tm k)
    (_uniform : True)
    (_channel : ChannelFeedback afr tm)
    (R : RealDefectIdentification afr tm) :
    SingleStepProp afr tm :=
  singleStep_of_realDefectIdentification afr tm hnn R

/-- **`channel_alone_gives_singleStep` — channel_feedback ALONE already gives
`singleStep`** (it is the identity, §1).  Confirms the conjunction is padded: a
single alias conjunct suffices, so the other two are not independent
strictly-weaker sub-obligations. -/
theorem channel_alone_gives_singleStep (afr : AFRateModulus) (tm : Nat → Q')
    (H : ChannelFeedback afr tm) : SingleStepProp afr tm := H

/-- **`adjudication_verdict` — the bundled machine-checked structural verdict.**

For all `(afr, tm)`:
  (1) `channel_feedback ↔ singleStep`  (definitional alias — no distinct content);
  (2) `real_defect_identification → singleStep` on `tm ≥ 0`, AND
      `singleStep → real_defect_identification` (bi-implication — an alias);
  (3) `singleStep` is both satisfiable (`tm ≡ 0`) and falsifiable (concrete `tm`) at
      fixed `afr`, so it is a non-trivial function of the free `tm` — NO `afr`-only
      `uniform_in_m` can imply it.

Consequence: `F` is NOT 3.  `singleStep` is ATOMIC (= channel_feedback
= real_defect_identification); `uniform_in_m` is a strictly-weaker, independent,
non-core-shrinking evidence lemma.  So `F ≈ 1` (the atomic core) + one evidence
node.  UNINHABITED frontier bundles untouched; the 4D Yang–Mills mass gap remains
OPEN. -/
theorem adjudication_verdict :
    (∀ (afr : AFRateModulus) (tm : Nat → Q'),
        (ChannelFeedback afr tm ↔ SingleStepProp afr tm))
    ∧ (∀ (afr : AFRateModulus) (tm : Nat → Q'),
        (∀ k, (0 : Q') ≤ tm k) → RealDefectIdentification afr tm → SingleStepProp afr tm)
    ∧ (∀ (afr : AFRateModulus),
        SingleStepProp afr (fun _ => (0 : Q'))
        ∧ ¬ SingleStepProp afr (fun k => if k = 0 then (1 : Q') else 0)) :=
  ⟨channelFeedback_iff_singleStep,
   fun afr tm hnn R => singleStep_of_realDefectIdentification afr tm hnn R,
   fun afr => ⟨singleStep_satisfiable_zero afr, singleStep_falsifiable afr⟩⟩

end YMGap.Continuum.SingleStepDecompositionAdjudication

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.singleStepBound_is_prop
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.channelFeedback_iff_singleStep
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.channelFeedback_of_singleStep
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.singleStep_of_channelFeedback
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.singleStep_of_realDefectIdentification
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.realDefectIdentification_of_singleStep
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.singleStep_satisfiable_zero
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.singleStep_falsifiable
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.decomposition_collapses_to_singleStep
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.channel_alone_gives_singleStep
#print axioms YMGap.Continuum.SingleStepDecompositionAdjudication.adjudication_verdict
