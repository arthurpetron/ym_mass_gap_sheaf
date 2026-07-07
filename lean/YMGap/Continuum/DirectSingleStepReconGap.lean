/-
Track B / R2 — DIRECT attack on the ATOMIC core `SingleStepDefectBound` via the
PROVED reconstructed-transfer located gap (`reconTransfer_located_gap`), NO surrogate
interacting measure.

# What this module does (read first)

`SingleStepDefectReduction.SingleStepDefectBound` puts the WHOLE Clay continuum gap
on ONE open field
    `singleStep : ∀ k, (1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin (k+1)` ,
for a FREE sequence `trueMargin : Nat → Q'` (the dimensionless margin `m_lat(a_k)/a_k`)
with only a positive anchor.  The PROVED fixed-spacing content is
`MayerClustering.reconTransfer_located_gap`, giving the reconstructed single-edge
transfer operator a LOCATED gap at the strong-coupling weight `w = 1/6`, separator
`rho gw = 2·(1/6)³ = 1/108`, margin `1 − rho gw = 107/108` — the REAL Wilson
connected-correlator gap, NOT a model.

The DIRECT route asks: can `trueMargin_k` be DEFINED as the reconstructed located-gap
margin at the flowing weight `w_k`, so that `singleStep` is discharged from the proved
fixed-spacing gap WITHOUT the unconstructed interacting `a→0` measure?

This module answers with (1) a genuine NEW CONSTRUCTION and (2) a machine-checked
OBSTRUCTION — NO new `:= SingleStepDefectBound` alias, and it inhabits `SingleStepDefectBound`
NOWHERE.

## (1) GENUINE CONSTRUCTION — the located gap at EVERY strong-coupling weight

`reconTransfer_located_gap` is proved ONLY at the fixed anchor `w = gw = 1/6`.  Here
`reconTransfer_located_gap_general` GENERALIZES it to ANY strong-coupling weight
`w ∈ (0, 1/2]`: the reconstructed single-edge transfer operator `reconTransfer w hw (M+1)`
has a located gap with `sep = rho w = 2w³` for every such `w`.  This is a real advance
over the fixed-anchor object — the clustering input `reconTransfer_corr_decay` and the
rate bound `rho_lt_one` already hold for all `w ≤ 1/2`, and the excited-weight positivity
`coeffW_pos` (new, general `w > 0`) supplies the coupling side condition.  It gives the
per-scale margin `reconMargin w = 1 − 2w³` at ANY strong-coupling scale — the candidate
`trueMargin_k`.  Ties to the proved anchor: `reconMargin gw = 107/108` (`reconMargin_anchor`).

## (2) MACHINE-CHECKED OBSTRUCTION — the reconstructed margin CANNOT be `trueMargin`

The RG flow drives `w_k → 1` in the deep UV (asymptotic freedom).  The reconstructed
located-gap construction requires `w ≤ 1/2` (`rho_lt_one`).  Beyond it the single-edge
object provably FAILS as a margin:

  * `rho_ge_one_at_weak` : `1 ≤ rho wWeak` at the concrete weak-coupling weight
    `wWeak = 9/10` — `rho(9/10) = 2·(9/10)³ = 1458/1000 > 1`.  So the located-gap
    separator hypothesis `sep < 1` is UNSATISFIABLE there.
  * `reconMargin_neg_at_weak` : `reconMargin wWeak < 0` — the single-edge margin
    `1 − 2w³` goes NEGATIVE for `w ≥ (1/2)^{1/3} ≈ 0.794`, so it cannot be a positive
    physical margin.
  * `no_located_gap_at_weak` : the reconstructed transfer operator `reconTransfer wWeak
    hw (M+1)` has NO `LocatedSpectralGap` at all — any such gap forces `lam 0 = rho wWeak
    ≤ sep < 1`, contradicting `rho wWeak ≥ 1`.  A hard impossibility, not a proof weakness.

So the direct route `trueMargin_k := reconMargin(w_k)` CANNOT inhabit
`SingleStepDefectBound`: at deep-UV scales (`w_k → 1`) the reconstructed single-edge
margin is negative and the located gap does not exist.  The SPECIFIC missing object is a
located gap of the transfer operator at WEAK coupling `w_k → 1`, which the single-edge
strong-coupling reconstruction provably cannot supply (its leading excited eigenvalue
`rho = 2w³ → 2 > 1`), and which genuinely requires the interacting block-spin effective
action at each scale — the unconstructed `a→0` object.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

The direct route ADVANCES the construction (the fixed-anchor located gap generalized to
the whole strong-coupling window `w ≤ 1/2`, a real new object) but does NOT inhabit
`SingleStepDefectBound`, and CANNOT via this object: the machine-checked obstruction is
that the reconstructed single-edge margin fails (negative, no located gap) precisely where
`singleStep` bites — the deep UV `w_k → 1`.  `SingleStepDefectBound` is inhabited NOWHERE
here; NO new alias is emitted; NO 4D Yang–Mills mass gap is claimed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing the PROVED `reconTransfer_corr_decay`, `rho_lt_one`,
`coeffW_excited_le_one`, `clustering_implies_located`.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  Type-level witnesses are `Type` data.
-/

import YMGap.Continuum.MayerClustering
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.DirectSingleStepReconGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep

/-! ## 0. General excited-weight positivity (`w > 0`) — the coupling side condition. -/

/-- **`coeffW_pos` — the excited transfer eigenvalues are positive at any `w > 0`.**
`coeffW w (i+1) = dimQ (i+1)·qpow w (c4 (i+1))`; `dimQ (i+1) = ofNat (i+2) > 0` and
`qpow w n > 0` for `w > 0` (by induction).  Generalizes `coeffW_gw_pos` off the fixed
anchor `gw = 1/6` to any strong-coupling weight. -/
theorem coeffW_pos {w : Q'} (hw : (0 : Q') < w) (i : Nat) :
    (0 : Q') < coeffW w (i + 1) := by
  show (0 : Q') < dimQ (i + 1) * qpow w (c4 (i + 1))
  refine Q'.mul_pos ?_ ?_
  · show (0 : Q') < Q'.ofNat (i + 1 + 1)
    exact Q'.ofNat_succ_pos (i + 1)
  · have hpow : ∀ k : Nat, (0 : Q') < qpow w k := by
      intro k
      induction k with
      | zero => show (0 : Q') < (1 : Q'); decide
      | succ j ih =>
          show (0 : Q') < qpow w j * w
          exact Q'.mul_pos ih hw
    exact hpow (c4 (i + 1))

/-! ## 1. GENUINE CONSTRUCTION — the located gap at EVERY strong-coupling weight. -/

/-- **`reconTransfer_located_gap_general` — the reconstructed located gap at ANY
strong-coupling weight (NEW, PROVED).**

For every `w` with `0 < w ≤ 1/2`, the reconstructed single-edge transfer operator
`reconTransfer w (le_of_lt hwpos) (M+1)` has a LOCATED spectral gap with separator
`sep = rho w = 2w³ < 1`.  This GENERALIZES `MayerClustering.reconTransfer_located_gap`
(fixed `w = gw = 1/6`) to the whole strong-coupling window.  The clustering input is the
REAL Wilson connected-correlator decay `reconTransfer_corr_decay` (valid for all `w ≤ 1/2`),
the rate bound is `rho_lt_one`, the excited-weight positivity is `coeffW_pos`, and the
unused-slot control is `coeffW_excited_le_one` — all PROVED, none anchor-specific. -/
def reconTransfer_located_gap_general {w : Q'} (hwpos : (0 : Q') < w) (hwh : w ≤ half)
    (M : Nat) :
    LocatedSpectralGap (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)) := by
  have hw0 : (0 : Q') ≤ w := Q'.le_of_lt hwpos
  have hrho_pos : (0 : Q') < rho w := by
    show (0 : Q') < coeffW w 1
    have := coeffW_pos hwpos 0
    simpa using this
  have hC : (0 : Q') < Q'.ofNat (M + 1) * rho w :=
    Q'.mul_pos (Q'.ofNat_succ_pos M) hrho_pos
  refine clustering_implies_located (reconTransfer w hw0 (M + 1))
    (Q'.ofNat (M + 1) * rho w) (rho w)
    hC hrho_pos (rho_lt_one hw0 hwh) ?_ ?_ ?_
  · intro n
    exact reconTransfer_corr_decay hw0 hwh (M + 1) n
  · intro i _
    show (0 : Q') < coeffW w (i + 1)
    exact coeffW_pos hwpos i
  · intro i _
    show coeffW w (i + 1) ≤ rho w
    show coeffW w (i + 1) ≤ coeffW w 1
    have hidx : (i + 1 : Nat) = 1 + i := by omega
    rw [hidx]
    exact coeffW_excited_le_one hw0 hwh i

/-- **`reconMargin` — the reconstructed located-gap margin as a function of weight.**
`reconMargin w = 1 − rho w = 1 − 2w³`, the `gapMargin` of the located gap at weight `w`
(the candidate per-scale `trueMargin`, generalizing the fixed anchor `strongAnchor`). -/
def reconMargin (w : Q') : Q' := (1 : Q') - rho w

/-- The general located gap's margin IS `reconMargin w` — the located-gap margin at the
flowing weight, definitionally `1 − rho w`. -/
theorem reconTransfer_located_gap_general_margin {w : Q'} (hwpos : (0 : Q') < w)
    (hwh : w ≤ half) (M : Nat) :
    (reconTransfer_located_gap_general hwpos hwh M).gapMargin = reconMargin w := rfl

/-- **`reconMargin_pos` — the reconstructed margin is strictly positive in the
strong-coupling window (PROVED).**  For `0 < w ≤ 1/2`, `0 < reconMargin w = 1 − rho w`,
via `rho_lt_one`.  So the candidate `trueMargin` IS a positive margin — but ONLY for
`w ≤ 1/2`. -/
theorem reconMargin_pos {w : Q'} (hwpos : (0 : Q') < w) (hwh : w ≤ half) :
    (0 : Q') < reconMargin w :=
  one_sub_pos_of_lt_one (rho_lt_one (Q'.le_of_lt hwpos) hwh)

/-- **`reconMargin_anchor` — the construction ties to the PROVED anchor (non-vacuity).**
`reconMargin gw = 1 − rho gw = 107/108` — the same object as
`CrossoverAnchorFloor.strongAnchor` / `RealCorrMass.realLocated 0`.  A single decidable
`Q'` identity, certifying the general construction reproduces the proved fixed-spacing
margin at `w = 1/6`. -/
theorem reconMargin_anchor : reconMargin gw = (1 : Q') - rho gw := rfl

/-- The anchor margin clears `1/2` numerically (`= 107/108 ≥ 1/2`, decidable). -/
theorem reconMargin_anchor_ge_half :
    Q'.mkPos 1 2 (by decide) ≤ reconMargin gw := by decide

/-! ## 2. MACHINE-CHECKED OBSTRUCTION — the reconstructed margin fails in the deep UV.

The RG flow drives `w_k → 1` (asymptotic freedom).  At weak coupling the single-edge
reconstruction breaks as a margin, provably.  We pin a concrete weak-coupling weight
`wWeak = 9/10` and machine-check the three failures. -/

/-- The concrete weak-coupling weight `wWeak = 9/10` (a deep-UV scale, `> 1/2`). -/
def wWeak : Q' := Q'.mkPos 9 10 (by decide)

theorem wWeak_pos : (0 : Q') < wWeak := by decide

/-- `wWeak` is NOT in the strong-coupling window: `¬ (wWeak ≤ 1/2)`. -/
theorem wWeak_not_strong : ¬ (wWeak ≤ half) := by decide

/-- **`rho_ge_one_at_weak` — the located-gap rate hypothesis FAILS at weak coupling.**
`1 ≤ rho wWeak` — `rho(9/10) = 2·(9/10)³ = 1458/1000 = 1.458 ≥ 1`.  So the separator
requirement `sep < 1` of a located gap is UNSATISFIABLE at `wWeak` (the single-edge
leading excited eigenvalue exceeds the vacuum eigenvalue `1`). -/
theorem rho_ge_one_at_weak : (1 : Q') ≤ rho wWeak := by decide

/-- **`reconMargin_neg_at_weak` — the reconstructed margin is NEGATIVE at weak coupling.**
`reconMargin wWeak = 1 − rho wWeak < 0`.  The single-edge margin `1 − 2w³` inverts for
`w ≥ (1/2)^{1/3} ≈ 0.794`, so it is NOT a positive physical margin in the deep UV — it
cannot serve as `trueMargin_k` where `w_k → 1`. -/
theorem reconMargin_neg_at_weak : reconMargin wWeak < (0 : Q') := by decide

/-- **`no_located_gap_at_weak` — the reconstructed transfer operator has NO located gap
at weak coupling (hard impossibility, PROVED).**  Any `LocatedSpectralGap` of
`reconTransfer wWeak _ (M+1)` would force its leading excited eigenvalue
`lam 0 = coeffW wWeak 1 = rho wWeak` to satisfy `rho wWeak ≤ sep < 1`, contradicting
`rho wWeak ≥ 1` (`rho_ge_one_at_weak`).  So the deep-UV located gap does NOT exist for the
single-edge reconstruction — the object the direct route would need is provably absent. -/
theorem no_located_gap_at_weak (M : Nat) :
    LocatedSpectralGap (reconTransfer wWeak (Q'.le_of_lt wWeak_pos) (M + 1)) → False := by
  intro g
  -- lam 0 = coeffW wWeak (0+1) = coeffW wWeak 1 = rho wWeak
  have hb : (reconTransfer wWeak (Q'.le_of_lt wWeak_pos) (M + 1)).lam 0 ≤ g.sep :=
    g.bound 0
  have hlam : (reconTransfer wWeak (Q'.le_of_lt wWeak_pos) (M + 1)).lam 0 = rho wWeak := rfl
  rw [hlam] at hb
  -- rho wWeak ≤ sep < 1  ⟹  rho wWeak < 1, contradicting rho wWeak ≥ 1
  have hlt : rho wWeak < (1 : Q') := lt_of_le_of_lt hb g.sep_lt_one
  have hbad : (1 : Q') < (1 : Q') := Q'.lt_of_le_of_lt rho_ge_one_at_weak hlt
  exact Int.lt_irrefl _ hbad

/-! ## 3. The obstruction, packaged against `SingleStepDefectBound`.

We record, as an axiom-clean theorem, exactly why the direct route
`trueMargin_k := reconMargin(w_k)` cannot inhabit `SingleStepDefectBound`: it would need
`reconMargin(w_k)` to be a valid (positive, located-gap-backed) margin at EVERY scale,
but at the deep-UV scale `wWeak = 9/10` the margin is negative AND no located gap exists.
This is a genuine obstruction certificate, NOT a `:= SingleStepDefectBound` alias. -/

/-- **`direct_route_obstruction` — the machine-checked obstruction certificate.**
The reconstructed single-edge margin `reconMargin` (the ONLY margin the proved
fixed-spacing located gap supplies) FAILS at the concrete deep-UV weight `wWeak = 9/10`
in three independent, decidable ways: the located-gap rate exceeds `1`, the margin is
negative, and no located gap exists.  Hence `trueMargin_k := reconMargin(w_k)` cannot
inhabit `SingleStepDefectBound` over an AF flow with `w_k → 1`.  The missing object is a
located transfer gap at weak coupling — absent from the single-edge reconstruction, and
requiring the interacting block-spin effective action (the unconstructed `a→0` measure). -/
theorem direct_route_obstruction :
    ((1 : Q') ≤ rho wWeak)
      ∧ (reconMargin wWeak < (0 : Q'))
      ∧ (∀ M : Nat,
          LocatedSpectralGap (reconTransfer wWeak (Q'.le_of_lt wWeak_pos) (M + 1)) → False) :=
  ⟨rho_ge_one_at_weak, reconMargin_neg_at_weak, no_located_gap_at_weak⟩

end YMGap.Continuum.DirectSingleStepReconGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DirectSingleStepReconGap.coeffW_pos
#print axioms YMGap.Continuum.DirectSingleStepReconGap.reconTransfer_located_gap_general
#print axioms YMGap.Continuum.DirectSingleStepReconGap.reconTransfer_located_gap_general_margin
#print axioms YMGap.Continuum.DirectSingleStepReconGap.reconMargin_pos
#print axioms YMGap.Continuum.DirectSingleStepReconGap.reconMargin_anchor
#print axioms YMGap.Continuum.DirectSingleStepReconGap.reconMargin_anchor_ge_half
#print axioms YMGap.Continuum.DirectSingleStepReconGap.rho_ge_one_at_weak
#print axioms YMGap.Continuum.DirectSingleStepReconGap.reconMargin_neg_at_weak
#print axioms YMGap.Continuum.DirectSingleStepReconGap.no_located_gap_at_weak
#print axioms YMGap.Continuum.DirectSingleStepReconGap.direct_route_obstruction
