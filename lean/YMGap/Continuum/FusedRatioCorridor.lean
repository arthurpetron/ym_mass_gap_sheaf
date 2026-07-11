/-
`FusedRatioCorridor` — Milestone 14.3, identifications (i) and (ii) at the
pilot: the normalized blocked eigenvalue DEFINED (exact division in the
rational substrate), its additive corridor PROVED from the 14.2 sandwich,
and the FIRST GENUINE INSTANCE of the margin recursion at the
strong-coupling anchor — kernel-checked end to end.

# What this closes

`MarginErosionBrick.margin_recursion_of_corridor` reduced the 14.3
recursion to: (i) exhibit `λ'` (normalized blocked) and `λ` (free) with
`λ' ≤ λ + ε`; (ii) prove the width-vs-margin comparison `ε ≤ δ·m`.  This
module does both:

  * `lamB w N s := boxSum w N s · recip (boxSum w N 0)` — the normalized
    blocked eigenvalue proxy, an EXACT rational (the vacuum is positive
    by `vacuum_ge_one`, so `recip` is the true reciprocal);
  * `lamB_corridor` — the additive corridor
      `lamB w N s ≤ 2·coeffW w s + intAmp N s·w⁶`
    for `1 ≤ s ≤ N`, `w ∈ [0,1]`: divide the cross-multiplied
    `boxSum_ratio_upper` by the blocked vacuum (`div_le_of_le_mul`, the
    general division brick — first use of exact reciprocals on the
    critical path);
  * **`pilot_anchor_recursion`** — at the anchor point `w₀ = 1/8`
    (pilot `N = 3`, `s = 1`, `δ₀ = 1/5000`) the recursion holds:
      `(1 − δ₀)·(1 − λ_free(w₀)) ≤ 1 − lamB w₀ 3 1`,
    with the width-vs-margin hypothesis `36·w₀⁶ ≤ δ₀·(1 − 4·w₀³)`
    discharged by kernel `decide` on exact rationals — the corridor is
    provably thin against the anchor margin exactly where reality-fact
    one (COMPACTNESS/strong coupling) says it must be.

# What remains open (AGENTS.md Rule 6)

The k-uniform version: run the SAME corridor at every scale of the AF
flow (`afr.w k` in place of `w₀`) with the summable `δ_k` demanded by
anchor dominance — the width-vs-margin comparison as a THEOREM in `w` on
the flow's window, not a point check.  Then `recursion` is inhabited and
14.4's proved arrows assemble `singleStep`.  No frontier type is touched;
the Clay problem stays OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` core; exact reciprocal (`Q'.recip`) of the
positive vacuum.  Kernel `decide` on closed rationals only.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.MarginErosionBrick

namespace YMGap.Continuum.FusedRatioCorridor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusedChannelAll
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.FusedEnvelope
open YMGap.Continuum.MarginErosionBrick

/-! ## 1. Positivity and the division brick -/

/-- `1 ≤ V ⟹ 0 < V` (through the Int cross-product). -/
theorem pos_of_one_le {V : Q'} (h : (1 : Q') ≤ V) : (0 : Q') < V := by
  have h' : (1 : Int) * (V.den : Int) ≤ V.num * (1 : Int) := h
  show (0 : Int) * (V.den : Int) < V.num * (1 : Int)
  have hden : (0 : Int) < (V.den : Int) := by exact_mod_cast V.den_pos
  omega

/-- **The division brick.**  A cross-multiplied bound divides through by
a positive denominator: `X ≤ B·V`, `0 < V` gives `X·(1/V) ≤ B`. -/
theorem div_le_of_le_mul {X B V : Q'} (hV : (0 : Q') < V)
    (h : X ≤ B * V) : X * Q'.recip V ≤ B := by
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h
      (Q'.le_of_lt (Q'.recip_pos V))) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv B V (Q'.recip V)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left B _ _ (Q'.mul_recip_eqv V hV)) ?_
  exact Q'.mul_one_eqv B

/-! ## 2. The normalized blocked eigenvalue proxy -/

/-- `lamB w N s` — the blocked channel normalized by the blocked vacuum,
as an exact rational.  This is the object whose deviation from the free
flow the margin recursion consumes (the naive UNnormalized ratio was
machine-refuted in `IntAmpAnchors.naive_ratio_mismatch`). -/
def lamB (w : Q') (N s : Nat) : Q' :=
  boxSum w N s * Q'.recip (boxSum w N 0)

/-- **`lamB_corridor` (PROVED — identification (i)).**  The normalized
blocked eigenvalue sits in the additive corridor above the free part:

    lamB w N s ≤ (coeffW w s + coeffW w s) + intAmp N s·w⁶

for `1 ≤ s ≤ N`, `w ∈ [0, 1]` — exactly the `hcorr` hypothesis of
`margin_recursion_of_corridor`, with `λ = 2·c_s` and
`ε = intAmp N s·w⁶`. -/
theorem lamB_corridor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    {N s : Nat} (hs1 : 1 ≤ s) (hsN : s ≤ N) :
    lamB w N s
      ≤ (coeffW w s + coeffW w s) + intAmp N s * qpow w 6 := by
  have hV : (0 : Q') < boxSum w N 0 :=
    pos_of_one_le (vacuum_ge_one hw0 N)
  refine Q'.le_trans' _ _ _
    (div_le_of_le_mul hV (boxSum_ratio_upper hw0 hw1 hs1 hsN)) ?_
  exact Q'.ge_of_eqv
    (Q'.add_assoc_eqv (coeffW w s) (coeffW w s) (intAmp N s * qpow w 6))

/-! ## 3. The pilot anchor instance (kernel-checked) -/

/-- The pilot anchor coupling `w₀ = 1/8` (strong-coupling side). -/
def w0 : Q' := Q'.mkPos 1 8 (by omega)

/-- The pilot per-step erosion rate `δ₀ = 1/5000`. -/
def delta0 : Q' := Q'.mkPos 1 5000 (by omega)

/-- **Identification (ii) at the anchor (kernel `decide`).**  The
corridor width is dominated by `δ₀` times the free margin at `w₀`:
`36·w₀⁶ ≤ δ₀·(1 − 4·w₀³)` in exact rationals
(`36/262144·δ⁻¹-check: 1.37×10⁻⁴ ≤ 1.98×10⁻⁴`). -/
theorem anchor_width_le_margin :
    intAmp 3 1 * qpow w0 6
      ≤ delta0 * ((1 : Q') + -(coeffW w0 1 + coeffW w0 1)) := by decide

/-- **`pilot_anchor_recursion` (PROVED — the first genuine instance of
the 14.3 recursion).**  At the anchor `w₀ = 1/8`, pilot truncation
`N = 3`, channel `s = 1`: one blocking step erodes the margin by at most
the factor `(1 − δ₀)`,

    (1 − δ₀)·(1 − λ_free(w₀)) ≤ 1 − lamB w₀ 3 1,

assembled from the corridor (identification (i)), the kernel-checked
width-vs-margin bound (identification (ii)), and the conversion brick.
This is `SingleStepDefectBoundLoose.recursion`'s exact shape at scale 0. -/
theorem pilot_anchor_recursion :
    ((1 : Q') - delta0)
        * ((1 : Q') + -(coeffW w0 1 + coeffW w0 1))
      ≤ (1 : Q') + -(lamB w0 3 1) :=
  margin_recursion_of_corridor
    (Q'.eqv_refl _) (Q'.eqv_refl _)
    (lamB_corridor (by decide) (by decide)
      (by omega) (by omega : 1 ≤ 3))
    anchor_width_le_margin

end YMGap.Continuum.FusedRatioCorridor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedRatioCorridor.pos_of_one_le
#print axioms YMGap.Continuum.FusedRatioCorridor.div_le_of_le_mul
#print axioms YMGap.Continuum.FusedRatioCorridor.lamB_corridor
#print axioms YMGap.Continuum.FusedRatioCorridor.anchor_width_le_margin
#print axioms YMGap.Continuum.FusedRatioCorridor.pilot_anchor_recursion
