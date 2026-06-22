/-
Layer 0a (L0a) of the strong-coupling cluster-expansion build — the **genuine
per-plaquette character-activity bound** derived from the proved per-rep / Casimir
arithmetic, replacing the hardcoded Python fiducials.

# What this module delivers

The single-plaquette SU(2) heat-kernel weight expands in characters with the
diagonal coefficient `coeffW w s = dimQ s · w^{C₄(s)} = (s+1)·w^{s(s+2)}`
(`RGTransport.charFunc`).  The cluster-expansion *plaquette activity* is the
EXCITED-rep mass — the sum over the non-vacuum modes `s ≥ 1`:

    plaqActivity w M  :=  ∑_{1 ≤ s < 1+M}  coeffW w s   =   ∑_{k < M} coeffW w (1 + k).

The vacuum `s = 0` (`coeffW w 0 = 1`, the normalization) is excluded: the activity
is the weight the excited representations carry, which is what the polymer / KP
criterion treats as the small parameter at strong coupling (small `w`).  Its
leading term is `coeffW w 1 = (dim 1)·w^{C₄(1)} = 2·w³` (`heatKernelSep`'s
multiplicity-weighted leading atom).

The deliverables, all GENUINE arithmetic (no fiducial):

  * `coeffW_eq_tailTerm` — the identification `coeffW w s = tailTerm w 1 s`,
    wiring the activity onto the proved Casimir-tail engine.
  * `coeffW_succ_ratio` — the consecutive-rep decay
    `coeffW w (s+1) ≤ (2·w⁵)·coeffW w s`  for `s ≥ 1`,
    from the proved per-term Casimir-gain ratio (`tailTerm_ratio_gen`,
    `C₄(s+1)−C₄(s) = 2s+3 ≥ 5`, dim ratio `(s+2)/(s+1) ≤ 2`).
  * `ratio_le_half` — at strong coupling `0 ≤ w ≤ 1/2` the ratio is `≤ 1/2`
    (in fact `2w⁵ ≤ 1/16`); the explicit strong-coupling threshold is `w₀ = 1/2`.
  * `plaqActivity_le` — the activity bound
    `plaqActivity w M ≤ 4·w³` for all `M`, valid for `0 ≤ w ≤ 1/2`,
    via the proved geometric-series engine (`CharacterTail.geom_series_le`) at
    head `2w³`, ratio `2w⁵ ≤ 1/2`, closed-form bound `4w³ = 2w³/(1 − 1/2)`.

# Strong-coupling threshold and explicit constant (honest statement)

The clean closed form is `plaqActivity w ≤ 2w³/(1 − r)` with ratio `r = 2w⁵`.  We
state it at the worst-case `r = 1/2` (the threshold `w₀ = 1/2`), giving the
explicit constant `4w³`.  This SUPERSEDES the hardcoded Python fiducials
`Sheaf/SU2KP.rho_sf` / `Constructive/ExpBound.Z_upper = 1/1000` with derived
character arithmetic: the excited-rep activity is now a PROVED function of `w`,
not a posited rational.  (We do NOT edit those legacy modules; this is the genuine
derived replacement, documented as superseding them.)  At `w = 1/2` the bound is
`4·(1/2)³ = 1/2`; smaller `w` gives a cubically smaller activity — e.g. at
`w = 1/10`, `plaqActivity ≤ 4/1000`, of the same fiducial order as the old
`Z_upper = 1/1000` but DERIVED.

# Scope (underclaim, AGENTS.md Rule 6)

This is L0a: the genuine per-plaquette activity arithmetic.  It is NOT the cluster
expansion, NOT a KP convergence proof, NOT a 4D Yang–Mills mass gap.  It is the raw
input the L1 KP criterion consumes, with the fiducial replaced by derived math.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, reused proved order/ratio/geometric lemmas, and
`decide` on concrete decidable `Q'` facts.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm

namespace YMGap.Continuum.PlaquetteActivity

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm

/-! ## 0. The activity coefficient = the proved Casimir-tail term at degree 1

`coeffW w s = dimQ s · w^{C₄(s)} = (s+1)·w^{C₄(s)}` and the proved Casimir tail
term `tailTerm w 1 s = (s+1)^1·w^{C₄(s)}` coincide.  This identification lets the
activity reuse the proved per-term ratio engine `tailTerm_ratio_gen`. -/

/-- **The activity coefficient equals the degree-1 Casimir tail term.**
`coeffW w s = tailTerm w 1 s` (both `(s+1)·w^{C₄(s)}`; the only difference is
`dimQ s = ofNat(s+1)` vs. `ofNat((s+1)^1)`, equal by `(s+1)^1 = s+1`). -/
theorem coeffW_eq_tailTerm (w : Q') (s : Nat) : coeffW w s = tailTerm w 1 s := by
  show dimQ s * qpow w (c4 s) = Q'.ofNat ((s + 1) ^ 1) * qpow w (c4 s)
  have h : (s + 1) ^ 1 = s + 1 := by rw [Nat.pow_one]
  rw [h]
  rfl

/-! ## 1. The plaquette activity (excited-rep mass, `s ≥ 1`)

The cluster-expansion plaquette activity is the EXCITED-rep weight: the sum over
the non-vacuum spins `s ≥ 1`, truncated to a window of `M` terms `s = 1, …, M`.
The vacuum `s = 0` (the normalization `coeffW w 0 = 1`) is excluded. -/

/-- **The plaquette activity** `plaqActivity w M = ∑_{1 ≤ s < 1+M} coeffW w s`,
the excited-rep (non-vacuum) character mass of the single-plaquette heat-kernel
weight, truncated to the first `M` excited modes.  The genuine cluster-expansion
activity parameter (small at strong coupling). -/
def plaqActivity (w : Q') (M : Nat) : Q' :=
  finSum (fun k => coeffW w (1 + k)) M

@[simp] theorem plaqActivity_zero (w : Q') : plaqActivity w 0 = 0 := rfl

/-- The activity is nonnegative for `0 ≤ w` (every excited coefficient is `≥ 0`). -/
theorem plaqActivity_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) :
    (0 : Q') ≤ plaqActivity w M := by
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      show (0 : Q') ≤ finSum (fun k => coeffW w (1 + k)) k + coeffW w (1 + k)
      exact Q'.zero_le_add _ _ ih (coeffW_nonneg hw (1 + k))

/-- The leading activity coefficient `coeffW w 1 = 2·w³` (`dim 1 = 2`,
`C₄(1) = 3`); the head of the geometric activity bound. -/
theorem coeffW_one_eq (w : Q') : coeffW w 1 = dimQ 1 * heatKernelSep w := coeffW_one w

/-! ## 2. The consecutive-rep ratio bound (genuine Casimir-gain decay)

The successive excited coefficients decay: `coeffW w (s+1) ≤ (2·w⁵)·coeffW w s`
for `s ≥ 1`.  This is the proved per-term Casimir ratio `tailTerm_ratio_gen` at
degree `m = 1`, cutoff `S = 1`: the Casimir increment `C₄(s+1)−C₄(s) = 2s+3 ≥ 5`
gives the gain `w^{2s+3} ≤ w⁵`, and the dimension ratio `(s+2)/(s+1) ≤ 2`. -/

/-- **The consecutive-rep activity ratio.**  On `0 ≤ w ≤ 1`, for every excited
spin `s ≥ 1`,

    coeffW w (s + 1)  ≤  (2 · w⁵) · coeffW w s.

The explicit ratio is `ratio(w) = ofNat 2 · w⁵`, from the proved Casimir-gain
ratio `tailTerm_ratio_gen` (degree `m = 1`, cutoff `S = 1`): the Casimir increment
`C₄(s+1) − C₄(s) = 2s+3 ≥ 2·1+3 = 5` (so `w^{2s+3} ≤ w⁵`) and the dimension ratio
`(s+2)/(s+1) ≤ 2`. -/
theorem coeffW_succ_ratio {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) (hs : 1 ≤ s) :
    coeffW w (s + 1) ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w s := by
  -- reduce to tailTerm via the identification, then fire tailTerm_ratio_gen at m=1, S=1
  rw [coeffW_eq_tailTerm w (s + 1), coeffW_eq_tailTerm w s]
  -- tailTerm_ratio_gen gives ratio (ofNat (2^1) · qpow w (2·1+3)) = ofNat 2 · qpow w 5
  have hr := tailTerm_ratio_gen hw0 hw1 1 1 s hs
  -- hr : tailTerm w 1 (s+1) ≤ (ofNat (2^1) · qpow w (2*1+3)) · tailTerm w 1 s
  -- 2^1 = 2 and 2*1+3 = 5 are definitional Nat reductions
  exact hr

/-- **Strong-coupling ratio control.**  At `0 ≤ w ≤ 1/2` the activity ratio is
`≤ 1/2`: in fact `ofNat 2 · w⁵ ≤ ofNat 2 · (1/2)⁵ = 1/16 ≤ 1/2`.  The explicit
strong-coupling threshold is `w₀ = 1/2`. -/
theorem ratio_le_half {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ Q'.mkPos 1 2 (by decide)) :
    Q'.ofNat 2 * qpow w 5 ≤ Q'.mkPos 1 2 (by decide) := by
  -- w⁵ ≤ (1/2)⁵ by monotonicity, then 2·(1/2)⁵ = 1/16 ≤ 1/2.
  have hmono : qpow w 5 ≤ qpow (Q'.mkPos 1 2 (by decide)) 5 :=
    qpow_mono hw0 hw 5
  have hstep : Q'.ofNat 2 * qpow w 5 ≤ Q'.ofNat 2 * qpow (Q'.mkPos 1 2 (by decide)) 5 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmono (zero_le_ofNat 2)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- ofNat 2 · (1/2)^5 = 2/32 = 1/16 ≤ 1/2, decidable
  decide

/-! ## 3. The activity bound (genuine geometric closure)

At strong coupling `0 ≤ w ≤ 1/2` the activity is bounded by the closed-form
geometric sum `2w³/(1 − r)` with ratio `r = 2w⁵ ≤ 1/2`.  At the worst case
`r = 1/2` this is `4w³`.  Proved by the geometric-series engine
`CharacterTail.geom_series_le` at head `coeffW w 1 = 2w³`, ratio `2w⁵`, and the
closed-form dominator `H = 4w³` (which satisfies `head + r·H ≤ H`). -/

/-- The geometric-recurrence check `head + r·H ≤ H` for `head = 2w³`, `r = 2w⁵`,
`H = 4w³`, at strong coupling `r ≤ 1/2`.  Concretely
`2w³ + (2w⁵)·(4w³) ≤ 4w³` ⟸ `(2w⁵)·(4w³) ≤ 2w³` ⟸ `2w⁵ ≤ 1/2`
(the `ratio_le_half` hypothesis), since `(2w⁵)·(4w³) = 4w³·(2w⁵) ≤ 4w³·(1/2) = 2w³`. -/
theorem activity_recurrence {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hr : Q'.ofNat 2 * qpow w 5 ≤ Q'.mkPos 1 2 (by decide)) :
    coeffW w 1 + (Q'.ofNat 2 * qpow w 5) * (Q'.ofNat 4 * heatKernelSep w)
      ≤ Q'.ofNat 4 * heatKernelSep w := by
  -- H = 4·w³ nonneg
  have hHnn : (0 : Q') ≤ Q'.ofNat 4 * heatKernelSep w :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 4) (heatKernelSep_nonneg hw0)
  -- r·H ≤ (1/2)·H  (mono right by H ≥ 0)
  have hrH : (Q'.ofNat 2 * qpow w 5) * (Q'.ofNat 4 * heatKernelSep w)
      ≤ Q'.mkPos 1 2 (by decide) * (Q'.ofNat 4 * heatKernelSep w) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hr hHnn
  -- (1/2)·(4·w³) ≃ coeffW w 1 = dimQ 1 · w³  (since (1/2)·4 = 2 = dimQ 1)
  have hhalfH : (Q'.mkPos 1 2 (by decide) * (Q'.ofNat 4 * heatKernelSep w)).eqv
      (coeffW w 1) := by
    rw [coeffW_one_eq w]
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 1 2 (by decide)) (Q'.ofNat 4)
        (heatKernelSep w))) ?_
    refine Q'.mul_eqv_congr_right _ _ (heatKernelSep w) ?_
    -- (1/2)·ofNat 4 ≃ dimQ 1
    show ((Q'.mkPos 1 2 (by decide)) * Q'.ofNat 4).eqv (dimQ 1)
    decide
  -- coeffW w 1 + r·H ≤ coeffW w 1 + (1/2)·H ≤ coeffW w 1 + coeffW w 1
  have hchain : coeffW w 1 + (Q'.ofNat 2 * qpow w 5) * (Q'.ofNat 4 * heatKernelSep w)
      ≤ coeffW w 1 + coeffW w 1 := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coeffW w 1) _ _ hrH) ?_
    exact Q'.add_le_add_left (coeffW w 1) _ (coeffW w 1) (Q'.le_of_eqv hhalfH)
  refine Q'.le_trans' _ _ _ hchain ?_
  -- coeffW w 1 + coeffW w 1 ≃ 4·w³ = H
  refine Q'.le_of_eqv ?_
  rw [coeffW_one_eq w]
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv (dimQ 1) (dimQ 1) (heatKernelSep w))) ?_
  refine Q'.mul_eqv_congr_right _ _ (heatKernelSep w) ?_
  show (dimQ 1 + dimQ 1).eqv (Q'.ofNat 4)
  decide

/-- **THE ACTIVITY BOUND (L0a, genuine).**  At strong coupling `0 ≤ w ≤ 1/2` the
single-plaquette excited-rep activity is bounded, uniformly in the truncation `M`,
by the closed-form geometric sum

    plaqActivity w M  ≤  4·w³        (= 2w³ / (1 − 1/2), head `2w³`, ratio `2w⁵ ≤ 1/2`).

PROOF.  The excited coefficient sequence `f k = coeffW w (1 + k)` has head
`f 0 = coeffW w 1 = 2w³`, successive ratio `f(k+1) ≤ (2w⁵)·f(k)` (the proved
`coeffW_succ_ratio`, since `1 + k ≥ 1`), the ratio is `≤ 1/2` (`ratio_le_half`),
and `H = 4w³` satisfies the geometric recurrence (`activity_recurrence`); so the
proved geometric-series engine `CharacterTail.geom_series_le` sums every window
under `4w³`.  This is the genuine derived per-plaquette activity — NO hardcoded
fiducial. -/
theorem plaqActivity_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (M : Nat) :
    plaqActivity w M ≤ Q'.ofNat 4 * heatKernelSep w := by
  -- w ≤ 1/2 ≤ 1
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw (by decide)
  -- the ratio bound at ≤ 1/2
  have hr : Q'.ofNat 2 * qpow w 5 ≤ Q'.mkPos 1 2 (by decide) := ratio_le_half hw0 hw
  -- ratio nonneg
  have hr_nn : (0 : Q') ≤ Q'.ofNat 2 * qpow w 5 :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 2) (qpow_nonneg w hw0 5)
  -- H = 4w³ nonneg
  have hH_nn : (0 : Q') ≤ Q'.ofNat 4 * heatKernelSep w :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 4) (heatKernelSep_nonneg hw0)
  -- head f 0 = coeffW w (1 + 0) = coeffW w 1 ≤ coeffW w 1 (reflexive)
  have hf0 : coeffW w (1 + 0) ≤ coeffW w 1 := by
    have : (1 + 0 : Nat) = 1 := rfl
    rw [this]; exact Q'.le_refl' _
  -- ratio domination of the shifted sequence: f(k+1) ≤ r · f(k)
  have hdom : ∀ k, coeffW w (1 + (k + 1))
      ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w (1 + k) := by
    intro k
    have hidx : (1 + (k + 1) : Nat) = (1 + k) + 1 := by omega
    rw [hidx]
    exact coeffW_succ_ratio hw0 hw1 (1 + k) (by omega)
  -- recurrence: coeffW w 1 + r·H ≤ H
  have hrec : coeffW w 1 + (Q'.ofNat 2 * qpow w 5) * (Q'.ofNat 4 * heatKernelSep w)
      ≤ Q'.ofNat 4 * heatKernelSep w :=
    activity_recurrence hw0 hw1 hr
  -- fire the geometric-series engine
  exact CharacterTail.geom_series_le (fun k => coeffW w (1 + k))
    (coeffW w 1) (Q'.ofNat 2 * qpow w 5) (Q'.ofNat 4 * heatKernelSep w)
    hr_nn hH_nn hf0 hdom hrec M

/-! ## 4. Fiducial supersession — the derived replacement (honest)

The hardcoded Python fiducials `Sheaf/SU2KP.rho_sf` (`= 25/3`) and
`Constructive/ExpBound.Z_upper` (`= 1/1000`) were posited rational stand-ins for
the small-field / large-field activity scale.  `plaqActivity_le` REPLACES that
fiducial input with derived character arithmetic: the excited-rep activity is now
a PROVED function of the weight, `plaqActivity w ≤ 4w³` on `0 ≤ w ≤ 1/2`, with the
explicit head `2w³`, ratio `2w⁵`, and threshold `w₀ = 1/2`.

We verify the derived bound lands in the FIDUCIAL REGIME: at a strong-coupling
weight `w = 1/10`, the activity is `≤ 4·(1/10)³ = 4/1000`, of the same order as the
old `Z_upper = 1/1000`, but now DERIVED rather than posited.  (Larger `w` gives a
larger — but still cubically controlled — activity; smaller `w` gives a cubically
smaller one.)  This is the honest supersession: the cluster-expansion activity
input is no longer a hardcoded constant. -/

/-- The strong-coupling demo weight `w = 1/10`. -/
def demoW : Q' := Q'.mkPos 1 10 (by decide)

theorem demoW_nonneg : (0 : Q') ≤ demoW := by decide
theorem demoW_le_half : demoW ≤ Q'.mkPos 1 2 (by decide) := by decide

/-- **The derived activity lands in the fiducial regime.**  At `w = 1/10`,
`plaqActivity (1/10) M ≤ 4·(1/10)³ = 4/1000` for every `M` — the same order as the
old hardcoded `Z_upper = 1/1000`, now DERIVED from the proved geometric activity
bound (`plaqActivity_le`) rather than posited.  The closed-form value
`4·heatKernelSep (1/10) = 4/1000` is checked by `decide`. -/
theorem plaqActivity_demo_le_fiducial (M : Nat) :
    plaqActivity demoW M ≤ Q'.mkPos 4 1000 (by decide) := by
  have h := plaqActivity_le demoW_nonneg demoW_le_half M
  refine Q'.le_trans' _ _ _ h ?_
  -- 4·(1/10)³ = 4/1000, decidable equality as ≤
  decide

end YMGap.Continuum.PlaquetteActivity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PlaquetteActivity.coeffW_eq_tailTerm
#print axioms YMGap.Continuum.PlaquetteActivity.plaqActivity_nonneg
#print axioms YMGap.Continuum.PlaquetteActivity.coeffW_one_eq
#print axioms YMGap.Continuum.PlaquetteActivity.coeffW_succ_ratio
#print axioms YMGap.Continuum.PlaquetteActivity.ratio_le_half
#print axioms YMGap.Continuum.PlaquetteActivity.activity_recurrence
#print axioms YMGap.Continuum.PlaquetteActivity.plaqActivity_le
#print axioms YMGap.Continuum.PlaquetteActivity.plaqActivity_demo_le_fiducial
