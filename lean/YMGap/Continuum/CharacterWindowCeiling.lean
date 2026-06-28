/-
Track B / R2 — pushing the STRONG character-clustering window UP to the
`ρ < 1` boundary, and PROVING the rigorous CEILING at `w = 2^{−1/3}`.

# The two facts this module establishes (honest scope, read first)

The single-line Wilson connected correlator clusters at the GEOMETRIC RATE
`ρ(w) = WilsonConnCorr.rho w = coeffW w 1 = 2·w³` (`WilsonConnCorr.wilsonG_decay`:
`wilsonG w (M+1) n ≤ (M·ρ)·ρ^n`).  The decay is genuine clustering exactly when
`ρ(w) < 1`, i.e.

    2·w³ < 1   ⟺   w³ < 1/2   ⟺   w < 2^{−1/3} ≈ 0.7937.

The existing assembly (`WilsonConnCorr.wilsonG_decay`, `rho_lt_one`) is GATED at
the convenience bound `w ≤ 1/2`.  This module does two things:

  * **DELIVERABLE 1 — PUSH the proved window UP.**  Re-derives the excited-coefficient
    domination and the geometric decay at the larger explicit rational edge
    `wHi = 7/9 ≈ 0.7778` (strictly below `2^{−1/3}`, with `(7/9)³ = 343/729 <
    1/2 = 364.5/729`, so `ρ(7/9) = 686/729 < 1`).  This pushes the proved
    strong-clustering window's upper edge from `1/6 ≈ 0.167` (the old gate, the
    KP `CouplingWindow` edge) up to `7/9 ≈ 0.778` — most of the way to the
    middle.  Packaged as the first-class `WilsonWindow` object
    `strongWilsonWindowExt` (`hi = wHi`), whose decay field is GENUINELY proved.

  * **DELIVERABLE 2 — PROVE the CEILING.**  For `w³ ≥ 1/2` (`w ≥ 2^{−1/3}`) the
    rate is `ρ(w) = 2·w³ ≥ 1`, so the character/Mayer clustering bound `C·ρ^n`
    does NOT decay: there is NO character-mechanism clustering window above
    `2^{−1/3}`.  A concrete witness past the ceiling is `w = 4/5 = 0.8`
    (`(4/5)³ = 64/125 ≥ 1/2`, so `ρ(4/5) ≥ 1`).  Any `WilsonWindow` whose decay
    rate is `ρ` therefore has `hi³ < 1/2` (`hi < 2^{−1/3}`): the strong/character
    radius is provably bounded away from `w = 1`.

# Why the KP `TwoSidedGap.CouplingWindow` is NOT the object pushed here (honest)

`TwoSidedGap.CouplingWindow.gap` is phrased on the KP connecting-cluster sum
`clusterSpanSum (zChainClusterCountBound p) w gr d ≤ 2·ρ^d`, which the proved
`clusterSpanSum_decay` supplies ONLY under the KP threshold `kpRatio (…) w gr =
96·w³ ≤ 1/2`, i.e. `w ≤ (1/192)^{1/3} ≈ 0.1736`.  That KP ceiling is STRICTLY
BELOW the Wilson-rate ceiling `2^{−1/3}` (at `w = 7/9`, `kpRatio = 96·(7/9)³ ≈
45 ≫ 1` — the KP sum does NOT converge).  So the KP `CouplingWindow` genuinely
CANNOT be pushed to `wHi`, and we do NOT fake its `gap` field at `wHi`.  The
object whose ceiling really is `2^{−1/3}` is the single-line Wilson decay
`wilsonG_decay`, and that is what this module's `WilsonWindow` carries and
extends.  This is the honest target.

# The middle remains the open continuum problem (NOT faked)

Deliverable 1 reaches `wHi = 7/9 < 2^{−1/3}`; Deliverable 2 proves the character
mechanism cannot pass `2^{−1/3}`.  The region `[2^{−1/3}, 1]` — the
weak-coupling / continuum approach (`w → 1`) — has NO character-mechanism
clustering (`ρ ≥ 1`); a clustering window there requires a DIFFERENT,
non-perturbative mechanism = the open continuum problem.  The existing named
obligations `WeakCouplingGap.WeakClusteringBound` and
`WeakCouplingGap.RGClusteringTransport` stay UNCHANGED and UNINHABITED.  The
two-sided windows CANNOT meet via the character mechanism alone: the strong /
character radius is provably bounded at `2^{−1/3}`, strictly below `w = 1`.  NO
weak-coupling positivity is constructed; NO 4D Yang–Mills mass gap is claimed.

# Constructive contract (`lean/AGENTS.md`)

Mathlib-free; only `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `decide` on non-decidable props (the symbolic-`s` excited
domination is a REAL induction via the genuine `qpow_mono`; `decide` is used ONLY
on closed concrete-rational facts at the endpoint `wHi` / the witness `4/5`).  No
`sorry` / `admit` / new `axiom` / `Prop := True`.  The pushed window is genuinely
proved; the ceiling is a real inequality; `WeakClusteringBound` /
`RGClusteringTransport` are left uninhabited.
-/

import YMGap.Continuum.WilsonConnCorr
import YMGap.Continuum.MayerClustering
import YMGap.Continuum.TwoSidedGap

namespace YMGap.Continuum.CharacterWindowCeiling

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.WilsonConnCorr

/-- `¬ (a < b) ⟹ b ≤ a` on `Q'` (the order-trichotomy primitive, via
`Int.not_lt` on the cross-product representation).  Used to turn the
contradiction in the ceiling proof into the `1/2 ≤ hi³` hypothesis. -/
theorem le_of_not_lt' {a b : Q'} (h : ¬ (a < b)) : b ≤ a := by
  show b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  have h' : ¬ (a.num * (b.den : Int) < b.num * (a.den : Int)) := h
  exact Int.not_lt.mp h'

/-! ## 0. The explicit pushed edge `wHi = 7/9`

`wHi = 7/9 ≈ 0.7778` is a clean rational strictly below the irrational ceiling
`2^{−1/3} ≈ 0.7937`.  The two endpoint facts everything rests on are decidable
concrete-rational inequalities:

  * `(7/9)³ = 343/729 < 1/2 = 364.5/729`  (so `ρ(wHi) = 2·(7/9)³ < 1`);
  * `2·(7/9)⁵ = 33614/59049 ≤ 1`          (so the excited domination holds at `wHi`). -/

/-- **The pushed upper edge** `wHi = 7/9 ≈ 0.7778`, a clean rational strictly
below the ceiling `2^{−1/3} ≈ 0.7937`.  The proved strong-clustering window is
pushed from `1/6 ≈ 0.167` up to this edge. -/
def wHi : Q' := Q'.mkPos 7 9 (by decide)

/-- `wHi = 7/9 > 0` (non-vacuity of the interval `[0, wHi]`). -/
theorem wHi_pos : (0 : Q') < wHi := by decide

/-- **The genuine push:** `1/6 < wHi = 7/9` — the new edge is strictly above the
old strong-window edge `w₀ = 1/6`. -/
theorem wHi_gt_oldEdge : Q'.mkPos 1 6 (by decide) < wHi := by decide

/-- The cube of the edge is below `1/2`: `(7/9)³ = 343/729 < 1/2`.  This is the
`ρ < 1` boundary fact (decidable concrete rational). -/
theorem wHi_cube_lt_half : qpow wHi 3 < Q'.mkPos 1 2 (by decide) := by decide

/-- The edge is below the ceiling in the precise sense used by Deliverable 2:
`(7/9)³ < 1/2`, hence `wHi` is in the character-clustering region. -/
theorem wHi_below_ceiling : qpow wHi 3 < Q'.mkPos 1 2 (by decide) := wHi_cube_lt_half

/-! ## 1. DELIVERABLE 1a — the extended `ρ < 1` boundary

`ρ(w) = coeffW w 1 = dimQ 1 · qpow w 3 = 2·w³`.  For `w ≤ wHi`, by
cube-monotonicity (`qpow_mono`) `w³ ≤ (7/9)³ < 1/2`, so `ρ(w) = 2·w³ < 1`.  This
extends `WilsonConnCorr.rho_lt_one` (gated at `w ≤ 1/2`) up to the much larger
edge `wHi = 7/9`. -/

/-- **`rho_lt_one_ext` — the extended clustering-rate bound (PROVED).**

For `0 ≤ w ≤ wHi = 7/9`, the Wilson clustering rate is still `< 1`:

    rho w = coeffW w 1 = 2·w³ ≤ 2·(7/9)³ = 686/729 < 1.

By cube-monotonicity `qpow w 3 ≤ qpow wHi 3` (`qpow_mono`) scaled by `dimQ 1`,
then the decidable endpoint `2·(7/9)³ < 1`.  This pushes the proved `ρ < 1`
window's upper edge from `1/2` up to `7/9` (the genuine extension). -/
theorem rho_lt_one_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) :
    rho w < (1 : Q') := by
  unfold rho
  rw [coeffW_one_eq w]
  -- dimQ 1 · qpow w 3 ≤ dimQ 1 · qpow wHi 3 = 686/729 < 1
  have hsep : heatKernelSep w ≤ heatKernelSep wHi := heatKernelSep_mono hw0 hw
  have hstep : dimQ 1 * heatKernelSep w ≤ dimQ 1 * heatKernelSep wHi :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsep (dimQ_nonneg 1)
  refine HeatKernelGap.lt_of_le_of_lt hstep ?_
  -- dimQ 1 · (7/9)³ = 2 · 343/729 = 686/729 < 1, decidable
  show dimQ 1 * heatKernelSep wHi < (1 : Q')
  decide

/-- `ρ(w) ≥ 0` for `0 ≤ w` (reused from `WilsonConnCorr`). -/
theorem rho_nonneg_ext {w : Q'} (hw0 : (0 : Q') ≤ w) : (0 : Q') ≤ rho w :=
  WilsonConnCorr.rho_nonneg hw0

/-! ## 2. DELIVERABLE 1b — the extended excited-coefficient domination

`WilsonConnCorr.coeffW_excited_le_one` (every excited `coeffW w (1+k) ≤ coeffW w 1`)
is proved via `coeffW_succ_le_self`, which uses `ratio_le_half` (`2w⁵ ≤ 1/2`),
gated at `w ≤ 1/2`.  The genuine fact the non-increase actually needs is the
WEAKER `2w⁵ ≤ 1` (the ratio factor `≤ 1`), which holds up to `wHi`:
`2·(7/9)⁵ = 33614/59049 ≤ 1`.  We re-prove the one-step non-increase and its
all-`s` consequence at the extended edge `w ≤ wHi`, by the genuine per-rep ratio
`coeffW_succ_ratio` + cube/quintic monotonicity — NOT `decide` on symbolic `s`. -/

/-- The extended quintic-ratio control: for `0 ≤ w ≤ wHi`, `2·w⁵ ≤ 1`.  By
`qpow_mono` (`w⁵ ≤ (7/9)⁵`) and the decidable endpoint `2·(7/9)⁵ = 33614/59049 ≤
1`.  (Weaker than `ratio_le_half`'s `≤ 1/2`, but exactly what the non-increase
needs, and it holds on the much larger interval `[0, wHi]`.) -/
theorem ratio_le_one_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) :
    Q'.ofNat 2 * qpow w 5 ≤ (1 : Q') := by
  have hmono : qpow w 5 ≤ qpow wHi 5 := qpow_mono hw0 hw 5
  have hstep : Q'.ofNat 2 * qpow w 5 ≤ Q'.ofNat 2 * qpow wHi 5 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmono (by decide)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- 2 · (7/9)⁵ = 33614/59049 ≤ 1, decidable
  show Q'.ofNat 2 * qpow wHi 5 ≤ (1 : Q')
  decide

/-- **One step of the excited non-increase at the EXTENDED edge (PROVED).**  For
`0 ≤ w ≤ wHi` and `s ≥ 1`, `coeffW w (s+1) ≤ coeffW w s`.  The genuine per-rep
ratio `coeffW w (s+1) ≤ (2w⁵)·coeffW w s` (`coeffW_succ_ratio`) with the extended
`2w⁵ ≤ 1` (`ratio_le_one_ext`) and `coeffW ≥ 0`.  Mirrors
`WilsonConnCorr.coeffW_succ_le_self` but on `[0, wHi]` instead of `[0, 1/2]`. -/
theorem coeffW_succ_le_self_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (s : Nat) (hs : 1 ≤ s) :
    coeffW w (s + 1) ≤ coeffW w s := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
  have hratio : coeffW w (s + 1) ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w s :=
    coeffW_succ_ratio hw0 hw1 s hs
  have hr_le_one : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q') := ratio_le_one_ext hw0 hw
  have hcnn : (0 : Q') ≤ coeffW w s := coeffW_nonneg hw0 s
  have hstep : (Q'.ofNat 2 * qpow w 5) * coeffW w s ≤ (1 : Q') * coeffW w s :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hr_le_one hcnn
  refine Q'.le_trans' _ _ _ hratio (Q'.le_trans' _ _ _ hstep ?_)
  exact Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w s))

/-- **`coeffW_excited_le_rho_ext` — the extended excited domination (PROVED).**

At `0 ≤ w ≤ wHi = 7/9`, every excited coefficient is dominated by the head
`coeffW w 1 = rho w = 2w³`:

    coeffW w (1 + k)  ≤  coeffW w 1  =  rho w   for every `k`.

By the extended non-increase `coeffW_succ_le_self_ext` (a genuine induction on
`k`, NOT `decide` on symbolic `s`).  This is the domination `wilsonG_decay`'s
proof consumes, now valid up to the pushed edge `wHi`. -/
theorem coeffW_excited_le_rho_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) :
    ∀ k, coeffW w (1 + k) ≤ rho w := by
  intro k
  show coeffW w (1 + k) ≤ coeffW w 1
  induction k with
  | zero => exact Q'.le_refl' _
  | succ j ih =>
      have hidx : (1 + (j + 1) : Nat) = (1 + j) + 1 := by omega
      rw [hidx]
      exact Q'.le_trans' _ _ _
        (coeffW_succ_le_self_ext hw0 hw (1 + j) (by omega)) ih

/-! ## 3. DELIVERABLE 1c — the extended geometric DECAY of the real correlator

Re-derive the `wilsonG_decay` chain (collapse → excited domination → `(n+1)`-fold
power → `M`-term sum) at the extended edge `w ≤ wHi`.  Every step mirrors the
proved `w ≤ 1/2` case, but uses the EXTENDED domination `coeffW_excited_le_rho_ext`. -/

/-- Each collapsed excited term is `≤ ρ^{n+1}` at the extended edge:
`connChain w (1+k) n = (coeffW w (1+k))^{n+1} ≤ (rho w)^{n+1}` (excited base `≤`
head, both nonneg).  Mirrors `WilsonConnCorr.connChain_excited_le` on `[0, wHi]`. -/
theorem connChain_excited_le_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (k n : Nat) :
    connChain w (1 + k) n ≤ (rho w) ^ (n + 1) := by
  unfold connChain
  show (coeffW w (1 + k)) ^ (n + 1) ≤ (rho w) ^ (n + 1)
  exact pow_le_pow_of_le (coeffW_nonneg hw0 (1 + k))
    (coeffW_excited_le_rho_ext hw0 hw k) (n + 1)

/-- The collapsed connected sum is bounded by `(ofNat M)·ρ^{n+1}` at the extended
edge.  Induction on `M`, mirroring `WilsonConnCorr.connSum_le`. -/
theorem connSum_le_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) (M n : Nat) :
    connSum w M n ≤ Q'.ofNat M * (rho w) ^ (n + 1) := by
  unfold connSum
  induction M with
  | zero =>
      show (0 : Q') ≤ Q'.ofNat 0 * (rho w) ^ (n + 1)
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ k ih =>
      rw [finSum_succ]
      have hstep : finSum (fun j => connChain w (1 + j) n) k + connChain w (1 + k) n
          ≤ Q'.ofNat k * (rho w) ^ (n + 1) + (rho w) ^ (n + 1) := by
        refine Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ (connChain w (1 + k) n) ih) ?_
        exact Q'.add_le_add_left _ _ _ (connChain_excited_le_ext hw0 hw k n)
      refine Q'.le_trans' _ _ _ hstep ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((rho w) ^ (n + 1)) (Q'.ofNat_add_eqv k 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (Q'.ofNat k) (Q'.ofNat 1) ((rho w) ^ (n + 1))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 ((rho w) ^ (n + 1)) (by decide)) ?_
      exact Q'.one_mul_eqv ((rho w) ^ (n + 1))

/-- **`wilsonG_decay_ext` — the EXTENDED geometric decay (PROVED).**

For `0 ≤ w ≤ wHi = 7/9`, the real single-line Wilson connected correlator still
decays geometrically:

    wilsonG w (M+1) n  ≤  (ofNat M · rho w) · (rho w)^n,   rho w = 2w³ < 1.

The collapse `wilsonG_collapse` to the single-rep chain, the EXTENDED excited
domination `coeffW_excited_le_rho_ext`, and the `(n+1)`-fold power give the bound;
`rho_lt_one_ext` makes the rate `< 1` up to the pushed edge.  This is the genuine
clustering decay on `[0, wHi]` — up from the old `[0, 1/2]` gate. -/
theorem wilsonG_decay_ext {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi) (M n : Nat) :
    wilsonG w (M + 1) n ≤ (Q'.ofNat M * rho w) * (rho w) ^ n := by
  have hcol : wilsonG w (M + 1) n ≤ connSum w M n :=
    Q'.le_of_eqv (wilsonG_collapse w M n)
  refine Q'.le_trans' _ _ _ hcol (Q'.le_trans' _ _ _ (connSum_le_ext hw0 hw M n) ?_)
  refine Q'.le_of_eqv ?_
  show (Q'.ofNat M * (rho w) ^ (n + 1)).eqv ((Q'.ofNat M * rho w) * (rho w) ^ n)
  rw [Q'.pow_succ]
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat M) (rho w) ((rho w) ^ n))

/-! ## 4. DELIVERABLE 1d — the pushed window as a first-class object

`WilsonWindow` is the Wilson-correlator analogue of `TwoSidedGap.CouplingWindow`:
for every `w` in `[lo, hi]`, a rate `ρ < 1` together with the geometric Wilson
decay `wilsonG w (M+1) n ≤ (M·ρ)·ρ^n` for all `M, n`.  We inhabit it at
`hi = wHi = 7/9` (the GENUINE push, up from the KP `CouplingWindow` edge `1/6`),
its decay field DISCHARGED from `wilsonG_decay_ext`. -/

/-- **`WilsonWindow` — a first-class Wilson-clustering window (`Type`-level
data).**  For every weight `w` in `[lo, hi]`, a rate `ρ < 1` and the genuine
geometric decay of the real single-line Wilson connected correlator
`wilsonG w (M+1) n ≤ (ofNat M · ρ)·ρ^n` for all `M, n`, with `ρ = rho w`.  This
is the Wilson-mechanism analogue of `TwoSidedGap.CouplingWindow` (which is phrased
on the KP `clusterSpanSum` and is bounded at a LOWER edge `≈ 0.174`). -/
structure WilsonWindow : Type where
  /-- Lower endpoint of the window. -/
  lo : Q'
  /-- Upper endpoint of the window. -/
  hi : Q'
  /-- The window is a genuine non-degenerate interval. -/
  lo_le_hi : lo ≤ hi
  /-- The lower endpoint is in the nonnegative cone (needed for the decay). -/
  lo_nonneg : (0 : Q') ≤ lo
  /-- **The Wilson clustering witness on the window.**  For every `w` in
  `[lo, hi]` the rate `ρ = rho w` is `< 1` and the real Wilson correlator decays
  geometrically `wilsonG w (M+1) n ≤ (ofNat M · ρ)·ρ^n`. -/
  decay : ∀ w : Q', lo ≤ w → w ≤ hi →
    (rho w < (1 : Q')) ∧
      (∀ M n : Nat, wilsonG w (M + 1) n ≤ (Q'.ofNat M * rho w) * (rho w) ^ n)

/-- **`strongWilsonWindowExt` — the PUSHED Wilson window `[0, wHi] = [0, 7/9]`
(PROVED).**

The strong-clustering window of the single-line Wilson correlator, with `lo = 0`,
`hi = wHi = 7/9`.  The `decay` field is GENUINELY DISCHARGED: at each `w` in
`[0, 7/9]` the rate `ρ = rho w` is `< 1` by `rho_lt_one_ext` and the real
correlator decays by `wilsonG_decay_ext`.  This pushes the proved
strong-clustering edge from `1/6 ≈ 0.167` (the KP `CouplingWindow` edge) up to
`7/9 ≈ 0.778` — most of the way to the middle, and strictly below the ceiling
`2^{−1/3} ≈ 0.794`. -/
def strongWilsonWindowExt : WilsonWindow where
  lo := 0
  hi := wHi
  lo_le_hi := Q'.le_of_lt wHi_pos
  lo_nonneg := Q'.le_refl' 0
  decay := fun w hlo hhi =>
    ⟨ rho_lt_one_ext hlo hhi
    , fun M n => wilsonG_decay_ext hlo hhi M n ⟩

/-- The pushed window's upper endpoint is `wHi = 7/9` (definitional). -/
theorem strongWilsonWindowExt_hi : strongWilsonWindowExt.hi = wHi := rfl

/-- The pushed window's lower endpoint is `0` (definitional). -/
theorem strongWilsonWindowExt_lo : strongWilsonWindowExt.lo = 0 := rfl

/-- **The push is genuine:** the new edge `wHi = 7/9` strictly exceeds the old
strong-window edge `1/6` (`UniformCouplingGap.w0 = TwoSidedGap.strongWindow.hi`). -/
theorem strongWilsonWindowExt_pushes :
    Q'.mkPos 1 6 (by decide) < strongWilsonWindowExt.hi := wHi_gt_oldEdge

/-! ## 5. DELIVERABLE 2 — the CEILING theorem (the rigorous wall at `2^{−1/3}`)

For `w³ ≥ 1/2` (i.e. `w ≥ 2^{−1/3}`), the Wilson clustering rate is
`ρ(w) = 2·w³ ≥ 1`, so the clustering bound `C·ρ^n` does NOT decay.  No
character-mechanism window can contain such `w`. -/

/-- **`character_rate_ge_one_at_ceiling` — the rate hits `1` at the ceiling
(PROVED).**

For `w³ ≥ 1/2` (`w ≥ 2^{−1/3}`), the Wilson clustering rate is `≥ 1`:

    rho w  =  coeffW w 1  =  dimQ 1 · qpow w 3  =  2·w³  ≥  2·(1/2)  =  1.

(`dimQ 1 = 2`; `qpow w 3 = heatKernelSep w ≥ 1/2` by hypothesis; `2·(1/2) = 1`.)
A real inequality, not vacuous. -/
theorem character_rate_ge_one_at_ceiling {w : Q'}
    (hw : Q'.mkPos 1 2 (by decide) ≤ qpow w 3) :
    (1 : Q') ≤ rho w := by
  unfold rho
  rw [coeffW_one_eq w]
  -- 1 = dimQ 1 · (1/2) ≤ dimQ 1 · qpow w 3 = dimQ 1 · heatKernelSep w
  show (1 : Q') ≤ dimQ 1 * heatKernelSep w
  have hstep : dimQ 1 * Q'.mkPos 1 2 (by decide) ≤ dimQ 1 * heatKernelSep w :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hw (dimQ_nonneg 1)
  refine Q'.le_trans' _ _ _ ?_ hstep
  -- 1 ≤ dimQ 1 · (1/2) = 2 · 1/2 = 1, decidable
  show (1 : Q') ≤ dimQ 1 * Q'.mkPos 1 2 (by decide)
  decide

/-- **`no_character_clustering_above_ceiling` — no clustering above the ceiling
(PROVED).**

For `w³ ≥ 1/2` (`w ≥ 2^{−1/3}`), the rate is NOT `< 1` (`¬ (rho w < 1)`): the
character clustering bound `C·ρ^n` does not decay, so NO `WilsonWindow` built from
the character rate `ρ` can contain such `w`.  Directly from
`character_rate_ge_one_at_ceiling` (`1 ≤ ρ` contradicts `ρ < 1`). -/
theorem no_character_clustering_above_ceiling {w : Q'}
    (hw : Q'.mkPos 1 2 (by decide) ≤ qpow w 3) :
    ¬ (rho w < (1 : Q')) := by
  intro hlt
  have hge : (1 : Q') ≤ rho w := character_rate_ge_one_at_ceiling hw
  -- 1 ≤ rho w  and  rho w < 1  ⇒  False
  exact ClusteringImpliesGap.lt_irrefl' (rho w)
    (ClusteringImpliesGap.lt_of_lt_of_le hlt hge)

/-- **`character_ceiling_witness` — a concrete witness past the ceiling
(PROVED).**

At `w = 4/5 = 0.8 > 2^{−1/3} ≈ 0.794`, `(4/5)³ = 64/125 ≥ 1/2`, so the rate is
`≥ 1`:

    rho (4/5)  =  2·(4/5)³  =  128/125  ≥  1.

A real, non-vacuous instance of the ceiling. -/
theorem character_ceiling_witness :
    (1 : Q') ≤ rho (Q'.mkPos 4 5 (by decide)) := by
  refine character_rate_ge_one_at_ceiling ?_
  -- (4/5)³ = 64/125 ≥ 1/2, decidable
  show Q'.mkPos 1 2 (by decide) ≤ qpow (Q'.mkPos 4 5 (by decide)) 3
  decide

/-- The witness is genuinely past the pushed edge AND past the ceiling cube
boundary: `(4/5)³ = 64/125 ≥ 1/2 > 343/729 = (7/9)³`, so `4/5` lies in the
no-clustering region `[2^{−1/3}, 1)` (the rate fails `< 1`). -/
theorem character_ceiling_witness_no_clustering :
    ¬ (rho (Q'.mkPos 4 5 (by decide)) < (1 : Q')) :=
  no_character_clustering_above_ceiling (by decide)

/-- **`characterWindow_hi_lt_ceiling` — any Wilson window is bounded below the
ceiling (PROVED).**

Any `WilsonWindow` `W` whose lower endpoint is in the nonnegative cone and whose
upper endpoint `hi` is itself a window weight (`lo ≤ hi`) has `hi³ < 1/2`
(`hi < 2^{−1/3}`): the `decay` field forces `rho hi < 1` at `w = hi`, and by the
ceiling theorem (contrapositive) `rho hi < 1` forces `hi³ < 1/2`.  So the
strong / character window is provably bounded away from the weak region `w → 1`:
its upper edge CANNOT reach the ceiling `2^{−1/3}`. -/
theorem characterWindow_hi_lt_ceiling (W : WilsonWindow) :
    qpow W.hi 3 < Q'.mkPos 1 2 (by decide) := by
  -- At w = hi: rho hi < 1 (from the decay field at lo ≤ hi ≤ hi).
  have hrho : rho W.hi < (1 : Q') :=
    (W.decay W.hi W.lo_le_hi (Q'.le_refl' _)).1
  -- Decidable case-split on the goal `hi³ < 1/2`.  If it holds, done.  Otherwise
  -- `1/2 ≤ hi³` (le_of_not_lt'), so `1 ≤ rho hi` (ceiling theorem), contradicting
  -- `rho hi < 1` — the impossible branch is closed by absurdity.
  by_cases hlt : qpow W.hi 3 < Q'.mkPos 1 2 (by decide)
  · exact hlt
  · have hge : Q'.mkPos 1 2 (by decide) ≤ qpow W.hi 3 := le_of_not_lt' hlt
    exact absurd hrho (no_character_clustering_above_ceiling hge)

/-! ## 6. DELIVERABLE 3 — honest framing: the window reaches `wHi`, the ceiling
is `2^{−1/3}`, the middle past it is the open continuum problem.

We record the honest statements as named, PROVED facts (no faking):

  * the proved strong-clustering edge is `wHi = 7/9` (`strongWilsonWindowExt`),
    strictly above the old edge `1/6` and strictly below the ceiling;
  * the character mechanism CANNOT cross `2^{−1/3}` (`characterWindow_hi_lt_ceiling`,
    `no_character_clustering_above_ceiling`);
  * the region `[2^{−1/3}, 1]` has NO character clustering — a window there needs a
    DIFFERENT mechanism, the open continuum problem, carried by the UNCHANGED,
    UNINHABITED `WeakCouplingGap.WeakClusteringBound` / `RGClusteringTransport`. -/

/-- **`character_window_bounded_strictly_below_one` — the strong/character radius
is bounded away from `w = 1` (PROVED).**

Combining `characterWindow_hi_lt_ceiling` with the strict ceiling: any
`WilsonWindow` has `hi³ < 1/2`, and the ceiling cube boundary `1/2 < 1³` is
strict, so no window upper edge reaches `w = 1` (where `1³ = 1 ≥ 1/2`).  Concretely:
`W.hi³ < 1/2 ≤ (any w with w³ ≥ 1/2)³`.  The two-sided overlap therefore CANNOT
close via the character mechanism — the strong radius stops below `2^{−1/3} < 1`. -/
theorem character_window_bounded_strictly_below_one (W : WilsonWindow) :
    qpow W.hi 3 < qpow (1 : Q') 3 := by
  -- W.hi³ < 1/2 < 1 = 1³
  refine HeatKernelGap.lt_of_le_of_lt
    (Q'.le_of_lt (characterWindow_hi_lt_ceiling W)) ?_
  -- 1/2 < qpow 1 3 = 1, decidable
  show Q'.mkPos 1 2 (by decide) < qpow (1 : Q') 3
  decide

/-! ## 7. Documentation: PROVED vs the open continuum problem (AGENTS.md Rule 6)

PROVED here (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `wHi` (= `7/9`), `wHi_pos`, `wHi_gt_oldEdge`, `wHi_cube_lt_half` — the explicit
    pushed edge, strictly above the old edge `1/6` and below the ceiling;
  * `rho_lt_one_ext` — the clustering rate `ρ = 2w³ < 1` extended up to `wHi`
    (from `1/2`), via cube-monotonicity + the decidable endpoint `2·(7/9)³ < 1`;
  * `ratio_le_one_ext`, `coeffW_succ_le_self_ext`, `coeffW_excited_le_rho_ext` —
    the extended excited-coefficient domination `coeffW w (1+k) ≤ rho w` on
    `[0, wHi]` (genuine per-rep ratio + induction on `k`, NOT `decide` on
    symbolic `s`);
  * `connChain_excited_le_ext`, `connSum_le_ext`, `wilsonG_decay_ext` — the
    EXTENDED geometric decay `wilsonG w (M+1) n ≤ (M·ρ)·ρ^n` on `[0, wHi]`;
  * `WilsonWindow`, `strongWilsonWindowExt` (+ `_hi`, `_lo`, `_pushes`) — the
    pushed window as a first-class object, `hi = wHi = 7/9`, decay DISCHARGED;
  * `character_rate_ge_one_at_ceiling`, `no_character_clustering_above_ceiling`,
    `character_ceiling_witness` (+ `_no_clustering`),
    `characterWindow_hi_lt_ceiling`, `character_window_bounded_strictly_below_one`
    — the CEILING theorem: `ρ ≥ 1` for `w³ ≥ 1/2`, no clustering above the
    ceiling, the concrete witness `4/5`, and any window's upper edge `< 2^{−1/3}`.

NOT inhabited (UNCHANGED — the open continuum problem):

  * `WeakCouplingGap.WeakClusteringBound`, `WeakCouplingGap.RGClusteringTransport`
    — weak-coupling clustering on `[2^{−1/3}, 1]` and its RG transport through the
    middle.  This module does NOT touch them; they remain genuinely uninhabited.

HONEST SCOPE (underclaim).  The proved strong/character clustering window now
reaches `wHi = 7/9 ≈ 0.778` — up from `1/6 ≈ 0.167` — most of the way to the
middle.  The character/Mayer mechanism PROVABLY cannot cross the ceiling
`w = 2^{−1/3} ≈ 0.7937`: there the rate `ρ = 2w³ ≥ 1` and the clustering bound
does not decay (`no_character_clustering_above_ceiling`, witness `4/5`).  Every
`WilsonWindow` has `hi < 2^{−1/3}` (`characterWindow_hi_lt_ceiling`), so the
strong radius is bounded STRICTLY below `w = 1`
(`character_window_bounded_strictly_below_one`).  The region `[2^{−1/3}, 1]` —
the weak-coupling / continuum (`a → 0`) approach — has NO character-mechanism
clustering; a window there requires a DIFFERENT, non-perturbative mechanism =
the OPEN continuum problem.  The two-sided windows CANNOT meet via the character
mechanism alone.  NO weak-coupling positivity is constructed; NO 4D Yang–Mills
mass gap is claimed. -/

end YMGap.Continuum.CharacterWindowCeiling

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CharacterWindowCeiling.wHi_gt_oldEdge
#print axioms YMGap.Continuum.CharacterWindowCeiling.rho_lt_one_ext
#print axioms YMGap.Continuum.CharacterWindowCeiling.ratio_le_one_ext
#print axioms YMGap.Continuum.CharacterWindowCeiling.coeffW_succ_le_self_ext
#print axioms YMGap.Continuum.CharacterWindowCeiling.coeffW_excited_le_rho_ext
#print axioms YMGap.Continuum.CharacterWindowCeiling.connSum_le_ext
#print axioms YMGap.Continuum.CharacterWindowCeiling.wilsonG_decay_ext
#print axioms YMGap.Continuum.CharacterWindowCeiling.strongWilsonWindowExt
#print axioms YMGap.Continuum.CharacterWindowCeiling.strongWilsonWindowExt_pushes
#print axioms YMGap.Continuum.CharacterWindowCeiling.character_rate_ge_one_at_ceiling
#print axioms YMGap.Continuum.CharacterWindowCeiling.no_character_clustering_above_ceiling
#print axioms YMGap.Continuum.CharacterWindowCeiling.character_ceiling_witness
#print axioms YMGap.Continuum.CharacterWindowCeiling.characterWindow_hi_lt_ceiling
#print axioms YMGap.Continuum.CharacterWindowCeiling.character_window_bounded_strictly_below_one
