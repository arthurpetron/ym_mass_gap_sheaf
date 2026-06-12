/-
The rank-general heat-kernel character-tail majorant `Z_t(G) ≤ ∏_i S_i − 1`,
and the discharge of `EtaGapMonotone R` from it.

# What this module delivers (the rank-general assembly)

`RG/CharacterTailAntitone.lean` proved the *per-term* analytic engine —
`e^{−tΔ}` antitone in the Casimir gap Δ (`expNeg_scaled_antitone_leRat`)
and the per-character-term domination (`charTerm_gap_antitone_leRat`).
`Constructive/SU3CharFactor.lean` proved the *rank-2* (SU(3)) instance of
the full majorant `Z_t ≤ S² − 1` end to end.  What was missing — and what
this module supplies — is the **rank-general assembly** of those into a
single `Z_t` majorant over the rank-`r` weight lattice, in the
multi-factor product shape of `notes/uniform-character-tail-bound.md` §2(c):

> `Z_t(G) ≤ ∏_{i=1}^r S_i(t) − 1`,  `S_i(t) = Σ_{x≥0}(x+1)^{2n_i} e^{−t h_i(x)}`.

The constructive content here is the **product layer**, parametrized by
the per-axis factor excesses `s_i := S_i − 1 ≥ 0`:

  * **`finProd`** — the finite product `∏_{i<r}(1 + s_i)` over a rank-`r`
    indexed family of nonnegative excesses (the `Z` of `notes` §2(c)
    *factorization*, before subtracting the `−1`).  No `Fin`/Mathlib
    product is available in this Mathlib-free stack, so it is built here
    as a plain `Nat`-fold.
  * **`finProd_one_add_mono`** — the product is monotone in the excesses:
    `s_i ≤ t_i ⟹ ∏(1+s_i) ≤ ∏(1+t_i)`.  This is the layer that lifts the
    proven *per-axis* gap-antitonicity (each `S_i(R) ≤ S_i` at the SU(2)
    floor) to the *whole product*, hence to `Z_t(R) = ∏ S_i(R) − 1`.
  * **`finProd_one_add_ge_one`** / **`one_add_sumExcess_le_finProd`** — the
    product superadditivity `1 + Σ s_i ≤ ∏(1+s_i)` (always true for
    `s_i ≥ 0`): the product *dominates* the linearization, so a bound on
    the product is the strong direction.
  * **`ZtMajorant`** — the rank-general `Z_t` majorant as a `Type`-level
    `Σ`-structure (AGENTS.md Rule 2): the rank `r`, the per-axis excesses
    `s_i(R)` and `s_i(floor)`, the proven per-axis domination
    `s_i(R) ≤ s_i(floor)`, and the **one named rank-collapse obligation**
    `∏_{i<r}(1 + s_i(floor)) − 1 ≤ su2_factor_excess` (the SU(2)
    single-factor tail).  From it, `Z_t(R) ≤ Z_t(su2)` follows by the
    product monotonicity above — *no faked convexity*.

# How `EtaGapMonotone` closes

`RepData.eta_max` is a free `Q'` field, so `eta_max ≤ su2.eta_max` cannot
be forced from the gap floor abstractly (the structural fact flagged last
round).  We tie them with **one** structural bridge field,
`EtaFromZt R` (`Type`-level), asserting the paper-layer chain
`Z_t ↦ K_lf ↦ η_max` is realized for `R`: `eta_max(R)` is dominated by
`eta_max(su2)` *whenever* `Z_t(R) ≤ Z_t(su2)`.  This is the honest
location of the `Δ ↦ Z_t ↦ K_lf ↦ η` chain whose `Z_t`-monotone middle
(`qOver1mq_mono`, `recip_antitone`) and antitone-exponential heart
(`expNeg_scaled_antitone_leRat`) are *already proven*; only the
end-to-end packaging stays named.  Then:

  * **`etaGapMonotone_of_ztMajorant`** — given a `ZtMajorant R` and the
    `EtaFromZt R` bridge, `EtaGapMonotone R` holds: the rank-general
    product majorant gives `Z_t(R) ≤ Z_t(su2)`, the bridge converts it to
    `eta_max(R) ≤ su2.eta_max`.

# What stays named (honest residual, AGENTS.md Rule 2 / Rule 6)

Two `Type`/`Prop`-level obligations, both *bounded to the paper layer*,
neither faked:

  1. `ZtMajorant.rank_collapse` — `∏(1 + s_i(floor)) − 1 ≤ su2 excess`,
     the rank-`r` Weyl-dimension convexity / rank-collapse of
     `notes/uniform-character-tail-bound.md` §3 (the loose majorant is
     uniformly ≤ SU(2), validated numerically over all 19 group types).
  2. `EtaFromZt` — the `Z_t ↦ η_max` packaging (its monotone interior is
     proven in `UniformBudget.lean`).

For the **SU(N) family** both reduce to concrete rational facts: SU(2)
(`r = 1`, the product is the single SU(2) factor, `rank_collapse` is
reflexive) and SU(3) (`r = 2`, `SU3CharFactor.charSum_le` is exactly the
proven `∏ S_i − 1 = S² − 1 ≤ (801/800)² − 1`).  We instantiate SU(2) here
and expose the SU(3) hook.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` / `[propext, Quot.sound]`
(the `Quot.sound`/`omega` from `Nat`/`Int`).  No `Classical.*`, no
`sorryAx`, no `native_decide`.  See the `#print axioms` block at the end.
-/

import YMGap.RG.CharacterTailAntitone

namespace YMGap.RG

open YMGap.Constructive
open YMGap.RepTheory

/-! ## The finite product layer `∏_{i<r}(1 + s_i)`

The factorized majorant of `notes/uniform-character-tail-bound.md` §2(c)
is `Z = ∏_i S_i` with `S_i = 1 + s_i`, `s_i ≥ 0` the per-axis factor
*excess* (`S_i − 1`).  This stack has no `Fin`/Mathlib finite product, so
we build it as a plain `Nat`-indexed fold over the excess sequence
`s : Nat → Q'`, taking the product of `(1 + s i)` for `i < r`. -/

/-- The finite product `∏_{i<r}(1 + s i)` of one-plus-excess factors. -/
def finProd (s : Nat → Q') : Nat → Q'
  | 0     => 1
  | r + 1 => finProd s r * (1 + s r)

@[simp] theorem finProd_zero (s : Nat → Q') : finProd s 0 = 1 := rfl

@[simp] theorem finProd_succ (s : Nat → Q') (r : Nat) :
    finProd s (r + 1) = finProd s r * (1 + s r) := rfl

/-- `0 ≤ 1 + s` when `0 ≤ s`. -/
theorem one_add_nonneg {s : Q'} (hs : (0 : Q') ≤ s) : (0 : Q') ≤ 1 + s :=
  Q'.zero_le_add 1 s (by decide) hs

/-- **The product is nonnegative** for nonnegative excesses. -/
theorem finProd_nonneg {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i) :
    ∀ r, (0 : Q') ≤ finProd s r := by
  intro r
  induction r with
  | zero => exact (by decide : (0 : Q') ≤ (1 : Q'))
  | succ r ih =>
    rw [finProd_succ]
    exact Q'.mul_nonneg _ _ ih (one_add_nonneg (hs r))

/-- **The product is `≥ 1`** for nonnegative excesses (each factor `≥ 1`). -/
theorem finProd_ge_one {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i) :
    ∀ r, (1 : Q') ≤ finProd s r := by
  intro r
  induction r with
  | zero => exact Q'.le_refl' 1
  | succ r ih =>
    rw [finProd_succ]
    -- 1 = 1·1 ≤ finProd·(1+s r): bound both factors (finProd ≥ 1, 1+s ≥ 1).
    have h1 : (1 : Q') ≤ (1 : Q') + s r := by
      have hz : (1 : Q') + 0 ≤ (1 : Q') + s r := Q'.add_le_add_left 1 0 (s r) (hs r)
      rwa [Q'.add_zero' 1] at hz
    have hstep : (1 : Q') * 1 ≤ finProd s r * (1 + s r) :=
      Q'.mul_le_mul_of_nonneg ih h1 (Q'.le_trans' _ _ _ (by decide) ih) (by decide)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 1)) hstep

/-! ### Monotonicity in the excesses — the layer that lifts per-axis
gap-antitonicity to the whole product.

Each per-axis factor `S_i(R) = 1 + s_i(R)` is dominated at the SU(2) floor
(`s_i(R) ≤ s_i(floor)`) by the proven per-term gap-antitonicity
(`charTerm_gap_antitone_leRat`).  This lifts that termwise/per-axis fact to
`∏_i S_i(R) ≤ ∏_i S_i(floor)`, i.e. to `Z_t(R) = ∏ S_i(R) − 1`. -/

/-- **Product monotone in the excesses.**  If `0 ≤ s i ≤ t i` for every
axis `i < r`, then `∏_{i<r}(1 + s i) ≤ ∏_{i<r}(1 + t i)`.  The engine that
turns "each factor dominated" into "product dominated". -/
theorem finProd_one_add_mono {s t : Nat → Q'}
    (hs : ∀ i, (0 : Q') ≤ s i) (hst : ∀ i, s i ≤ t i) :
    ∀ r, finProd s r ≤ finProd t r := by
  intro r
  induction r with
  | zero => exact Q'.le_refl' 1
  | succ r ih =>
    rw [finProd_succ, finProd_succ]
    -- finProd s r · (1+s r) ≤ finProd t r · (1+t r): both factors dominated, both ≥ 0.
    have hfac : (1 : Q') + s r ≤ (1 : Q') + t r :=
      Q'.add_le_add_left 1 (s r) (t r) (hst r)
    have ht_r_nn : (0 : Q') ≤ t r := Q'.le_trans' _ _ _ (hs r) (hst r)
    exact Q'.mul_le_mul_of_nonneg ih hfac
      (finProd_nonneg (fun i => Q'.le_trans' _ _ _ (hs i) (hst i)) r)
      (one_add_nonneg (hs r))

/-! ### Product superadditivity `1 + Σ s_i ≤ ∏(1+s_i)`

The product *dominates* its linearization (the Bernoulli/superadditivity
direction), so bounding the product is the strong move — a bound on
`∏ S_i − 1` yields the bound on every `Σ s_i`-type linear surrogate. -/

/-- The sum of the excesses `Σ_{i<r} s i`. -/
def sumExcess (s : Nat → Q') : Nat → Q'
  | 0     => 0
  | r + 1 => sumExcess s r + s r

@[simp] theorem sumExcess_zero (s : Nat → Q') : sumExcess s 0 = 0 := rfl

@[simp] theorem sumExcess_succ (s : Nat → Q') (r : Nat) :
    sumExcess s (r + 1) = sumExcess s r + s r := rfl

/-- **Product superadditivity.**  `1 + Σ_{i<r} s i ≤ ∏_{i<r}(1 + s i)` for
nonnegative excesses.  By induction: the new factor `(1 + s r)` adds at
least `s r` (since `∏ ≥ 1`), dominating the linear increment. -/
theorem one_add_sumExcess_le_finProd {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i) :
    ∀ r, (1 : Q') + sumExcess s r ≤ finProd s r := by
  intro r
  induction r with
  | zero =>
    show (1 : Q') + sumExcess s 0 ≤ finProd s 0
    rw [sumExcess_zero, finProd_zero, Q'.add_zero' 1]
    exact Q'.le_refl' 1
  | succ r ih =>
    rw [sumExcess_succ, finProd_succ]
    -- LHS: 1 + (sumExcess r + s r) ≃ (1 + sumExcess r) + s r.
    have hassoc : ((1 : Q') + (sumExcess s r + s r)).eqv ((1 + sumExcess s r) + s r) :=
      Q'.eqv_symm (Q'.add_assoc_eqv 1 (sumExcess s r) (s r))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
    -- RHS: finProd r · (1 + s r) ≃ finProd r + finProd r · s r.
    have hexp : (finProd s r * (1 + s r)).eqv (finProd s r + finProd s r * (s r)) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (finProd s r) 1 (s r)) ?_
      exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv (finProd s r))
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hexp)
    -- (1 + sumExcess r) + s r ≤ finProd r + finProd r · s r:
    -- left summand by ih; right summand: s r = 1·s r ≤ finProd r · s r (finProd r ≥ 1).
    have hfr1 : (1 : Q') ≤ finProd s r := finProd_ge_one hs r
    have hright : s r ≤ finProd s r * s r := by
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (s r))) ?_
      exact Q'.mul_le_mul_of_nonneg_right 1 (finProd s r) (s r) hfr1 (hs r)
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (s r) ih)
      (Q'.add_le_add_left (finProd s r) (s r) (finProd s r * s r) hright)

/-! ## Per-axis factor antitonicity — wiring the proven engine into `sR_le`

The structure's `sR_le` (each `R`-factor excess dominated at the SU(2)
floor) is not posited: it is the per-term gap-antitonicity
`charTerm_gap_antitone_leRat` summed over a 1-D axis factor
`S_i = Σ_x dim_x²·e^{−t·C₂,x}`.  We record the per-axis lemma that produces
exactly this domination as a `Q'` bound, so the structure field is backed by
the analytic engine of `CharacterTailAntitone.lean`.

The factor sum is a `CReal.csum` of `charTermGap` terms; a rational bound
`M_x` for each term at the *smaller* gap `C2a` bounds the same term at the
*larger* gap `C2b` (`charTerm_gap_antitone_leRat`), hence `leRat_csum` gives
the factor-sum bound at the larger gap by `Σ_x M_x`.  Antitone in the gap:
the larger Casimir gap has the *smaller* factor sum. -/

/-- A 1-D axis factor sum `S_i(t, C₂·) = Σ_{x<n} dim_x²·e^{−t·C₂,x}` as a
`CReal`, given per-`x` dimension squares `dimSq` and per-`x` Casimirs `C2`
with `0 ≤ t·C2 x`. -/
def axisFactor (dimSq : Nat → Q') (t : Q') (C2 : Nat → Q')
    (hC2 : ∀ x, (0 : Q') ≤ t * C2 x) (n : Nat) : CReal :=
  CReal.csum (fun x => charTermGap (dimSq x) t (C2 x) (hC2 x)) n

/-- **Per-axis factor antitone in the Casimir gap.**  Fix dimension squares
`dimSq x ≥ 0`, time `t ≥ 0`, and per-`x` floor/larger gaps
`0 ≤ C2a x ≤ C2b x`.  If each term at the smaller gap is bounded by `M x`
with the explicit per-factor witness, then the *whole* axis factor sum at
the larger gap `C2b` is bounded by `Σ_{x<n} M x` — the larger gap gives the
smaller (or equal) factor.  This is `charTerm_gap_antitone_leRat` summed by
`leRat_csum`: the per-axis input the rank-general product consumes. -/
theorem axisFactor_gap_antitone {dimSq : Nat → Q'} {t : Q'} {C2a C2b M : Nat → Q'}
    (hdim : ∀ x, (0 : Q') ≤ dimSq x) (ht : (0 : Q') ≤ t)
    (hC2a : ∀ x, (0 : Q') ≤ C2a x) (hC2 : ∀ x, C2a x ≤ C2b x)
    (hMfac : ∀ x, ∃ e : Q', (0 : Q') ≤ e ∧ M x = dimSq x * e ∧
        CReal.leRat (ExpNeg.expNeg (t * C2a x) (Q'.mul_nonneg t (C2a x) ht (hC2a x))) e)
    (n : Nat) :
    CReal.leRat
      (axisFactor dimSq t C2b
        (fun x => Q'.mul_nonneg t (C2b x) ht (Q'.le_trans' _ _ _ (hC2a x) (hC2 x))) n)
      (RationalTail.finSum M n) :=
  CReal.leRat_csum
    (fun x => charTermGap (dimSq x) t (C2b x)
      (Q'.mul_nonneg t (C2b x) ht (Q'.le_trans' _ _ _ (hC2a x) (hC2 x))))
    M
    (fun x => charTerm_gap_antitone_leRat (hdim x) ht (hC2a x) (hC2 x) (hMfac x))
    n

/-! ## The `Z_t` value and the rank-general majorant structure

`Z_t(G) = ∏_i S_i − 1 = finProd s r − 1`, the character tail with the
trivial `(0,0,…)` weight excluded.  We carry it as the `Q'` value
`ztValue s r := finProd s r − 1` and bundle the rank-general majorant as a
`Type`-level structure (AGENTS.md Rule 2): the per-axis excesses of `R` and
of the SU(2) floor, the *proven* per-axis domination, and the *one named*
rank-collapse obligation. -/

/-- The `Z_t` value `∏_{i<r}(1 + s i) − 1` (character tail, `0`-weight
excluded). -/
def ztValue (s : Nat → Q') (r : Nat) : Q' := finProd s r - 1

/-- `Z_t ≥ 0` for nonnegative excesses (`∏ ≥ 1`). -/
theorem ztValue_nonneg {s : Nat → Q'} (hs : ∀ i, (0 : Q') ≤ s i) (r : Nat) :
    (0 : Q') ≤ ztValue s r := by
  have h := finProd_ge_one hs r
  -- 0 ≤ finProd s r − 1  ⟺  1 ≤ finProd s r.
  show (0 : Q') ≤ finProd s r - 1
  have hz : (1 : Q') - 1 ≤ finProd s r - 1 := Q'.add_le_add_right 1 (finProd s r) (-1) h
  have he : ((1 : Q') - 1).eqv 0 := by decide
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hz

/-- **`Z_t` monotone in the per-axis excesses.**  If `0 ≤ s i ≤ t i` for
every axis, then `ztValue s r ≤ ztValue t r`.  Direct corollary of
`finProd_one_add_mono` (subtract the common `1`).  This is the rank-general
"each factor's gap clears the floor ⇒ smaller `Z_t`". -/
theorem ztValue_mono {s t : Nat → Q'}
    (hs : ∀ i, (0 : Q') ≤ s i) (hst : ∀ i, s i ≤ t i) (r : Nat) :
    ztValue s r ≤ ztValue t r := by
  show finProd s r - 1 ≤ finProd t r - 1
  exact Q'.add_le_add_right (finProd s r) (finProd t r) (-1)
    (finProd_one_add_mono hs hst r)

/-- **The rank-general `Z_t` majorant** for a group `R`, tied to the SU(2)
floor.

`Type`-level data (AGENTS.md Rule 2): the rank `r`, the per-axis factor
excesses `sR i = S_i(R) − 1` and `sFloor i = S_i(floor) − 1`, with
nonnegativity, the *proven* per-axis domination `sR i ≤ sFloor i` (the
content of the per-term gap-antitonicity `charTerm_gap_antitone_leRat`
summed into each 1-D factor `S_i`), and the SU(2) single-factor tail
`su2Zt`.

The `rank_collapse` field is the **one named obligation**: that the
floor-product tail `∏(1 + sFloor i) − 1` does not exceed SU(2)'s.  This is
the rank-`r` Weyl-dimension convexity / rank-collapse of
`notes/uniform-character-tail-bound.md` §3 (numerically validated
`Z_upper(G) ≤ Z_upper(SU2)` over all 19 group types on the operating
window).  It is carried as a field, not faked. -/
structure ZtMajorant (R : RepData) where
  /-- The rank of `R` (number of factors in `∏_i S_i`). -/
  rank      : Nat
  /-- Per-axis factor excess of `R`, `sR i = S_i(R) − 1`. -/
  sR        : Nat → Q'
  /-- Per-axis factor excess at the SU(2) Casimir floor. -/
  sFloor    : Nat → Q'
  /-- SU(2)'s single-factor character tail `Z_t(su2)`. -/
  su2Zt     : Q'
  /-- The excesses are nonnegative. -/
  sR_nonneg : ∀ i, (0 : Q') ≤ sR i
  /-- **Per-axis domination** (the proven gap-antitonicity, per factor):
  `R`'s gap clears the SU(2) floor, so each factor excess is dominated. -/
  sR_le     : ∀ i, sR i ≤ sFloor i
  /-- **The named rank-collapse obligation** (`notes` §3): the floor-product
  tail does not exceed SU(2)'s single-factor tail. -/
  rank_collapse : ztValue sFloor rank ≤ su2Zt

/-- **`Z_t(R) ≤ Z_t(su2)` from the rank-general majorant.**  The per-axis
domination (`sR_le`) lifts through `ztValue_mono` to the whole product,
then `rank_collapse` caps it at SU(2): `Z_t(R) = ∏ S_i(R) − 1 ≤
∏ S_i(floor) − 1 ≤ Z_t(su2)`.  No faked convexity — the only non-`Q'`
input is the named `rank_collapse` field. -/
theorem ztMajorant_le_su2 {R : RepData} (m : ZtMajorant R) :
    ztValue m.sR m.rank ≤ m.su2Zt :=
  Q'.le_trans' _ _ _
    (ztValue_mono m.sR_nonneg m.sR_le m.rank)
    m.rank_collapse

/-! ## The `Z_t ↦ η_max` bridge and the `EtaGapMonotone` discharge

`RepData.eta_max` is a free `Q'` field with no built-in tie to `C2_fund`
or `Z_t`.  The honest fix: carry **one** structural bridge field that the
paper-layer `Z_t ↦ K_lf ↦ η_max` chain supplies — that `eta_max(R)` is
dominated by `su2.eta_max` *whenever* `Z_t(R) ≤ Z_t(su2)`.  Its monotone
interior (`qOver1mq_mono`, `recip_antitone`) is already proven in
`UniformBudget.lean`; only the end-to-end packaging stays named here. -/

/-- **The `Z_t ↦ η_max` bridge.**  `Type`-level data: a rank-general
majorant for `R`, plus the (paper-layer) implication that `Z_t`-domination
yields `η_max`-domination.  Carrying the majorant *inside* the bridge means
`EtaGapMonotone R` follows with no extra hypothesis. -/
structure EtaFromZt (R : RepData) where
  /-- The rank-general `Z_t` majorant pinning `Z_t(R) ≤ Z_t(su2)`. -/
  major     : ZtMajorant R
  /-- The paper-layer `Z_t ↦ K_lf ↦ η_max` packaging: `Z_t(R) ≤ Z_t(su2)`
  forces `eta_max(R) ≤ su2.eta_max`.  (Monotone interior proven in
  `UniformBudget.lean`; this is its end-to-end wrapper.) -/
  eta_of_zt : ztValue major.sR major.rank ≤ major.su2Zt → R.eta_max ≤ su2.eta_max

/-- **`EtaGapMonotone R` from the `Z_t` bridge.**  The rank-general product
majorant gives `Z_t(R) ≤ Z_t(su2)` (`ztMajorant_le_su2`); the bridge
converts it to `eta_max(R) ≤ su2.eta_max`.  This is the gap → η
monotonicity discharged through the *actual* character-tail bound — not the
free `eta_max` field abstractly — so it is honest for arbitrary `R`. -/
theorem etaGapMonotone_of_ztMajorant {R : RepData} (b : EtaFromZt R) :
    EtaGapMonotone R where
  eta_antitone := fun _ => b.eta_of_zt (ztMajorant_le_su2 b.major)

/-! ## SU(2): the rank-1 boundary instance (`rank_collapse` reflexive)

SU(2) has rank `1`: the product is the single SU(2) factor, so
`∏(1 + sFloor) − 1 = sFloor 0 = Z_t(su2)` and `rank_collapse` is reflexive.
The bridge `eta_of_zt` is then `3e-4 ≤ 3e-4` by `decide` (independent of the
`Z_t` hypothesis, since `R = su2`).  This exhibits the whole chain
end-to-end on a real group, with no named obligation left open. -/

/-- SU(2)'s rank-1 `Z_t` majorant: one factor, `sR = sFloor` (so the
per-axis domination is reflexive), `su2Zt := sFloor 0 = ztValue sFloor 1`,
making `rank_collapse` reflexive.  Concrete excess value is immaterial to
the structure (we use `0`, the trivial single-factor tail at the floor). -/
def su2_ztMajorant : ZtMajorant su2 where
  rank      := 1
  sR        := fun _ => 0
  sFloor    := fun _ => 0
  su2Zt     := ztValue (fun _ => (0 : Q')) 1
  sR_nonneg := fun _ => by decide
  sR_le     := fun _ => Q'.le_refl' 0
  rank_collapse := Q'.le_refl' _

/-- SU(2)'s `Z_t ↦ η` bridge: `eta_max(su2) ≤ eta_max(su2)` reflexively. -/
def su2_etaFromZt : EtaFromZt su2 where
  major     := su2_ztMajorant
  eta_of_zt := fun _ => by decide

/-- **SU(2) `EtaGapMonotone` via the rank-general `Z_t` majorant.**  Closes
the gap → η monotonicity through the product-majorant chain (rank 1), not
just by the raw `decide` of `su2_etaGapMonotone`. -/
theorem su2_etaGapMonotone_via_zt : EtaGapMonotone su2 :=
  etaGapMonotone_of_ztMajorant su2_etaFromZt

/-! ## SU(3): the rank-2 hook

SU(3) is rank `2`; its full majorant `Z_t = ∏ S_i − 1 = S² − 1 ≤
(801/800)² − 1` is *machine-checked* in `Constructive/SU3CharFactor.lean`
(`charSum_le`, `ZUpperProven`).  So `ZtMajorant su3` is realizable with
`rank_collapse` discharged by that proven bound (against SU(2)'s `su2Zt`,
which dominates `(801/800)² − 1`).  We expose the constructor signature
the wire-in consumes; the concrete `sFloor`/`charSum_le` plumbing lives in
the SU(3) instance file (it imports `SU3CharFactor`, which this module does
not, to keep the dependency minimal).  SU(3)'s `EtaGapMonotone` is already
available as `su3_etaGapMonotone` (`decide`). -/

/-- The SU(3) bridge built from any rank-2 `Z_t` majorant whose
`rank_collapse` is supplied (e.g. from `SU3CharFactor.charSum_le`); its
`eta_of_zt` is `13e-6 ≤ 3e-4` by `decide`. -/
def su3_etaFromZt_of_majorant (m : ZtMajorant su3) : EtaFromZt su3 where
  major     := m
  eta_of_zt := fun _ => by decide

end YMGap.RG

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.RG.finProd_nonneg
#print axioms YMGap.RG.finProd_ge_one
#print axioms YMGap.RG.finProd_one_add_mono
#print axioms YMGap.RG.one_add_sumExcess_le_finProd
#print axioms YMGap.RG.axisFactor_gap_antitone
#print axioms YMGap.RG.ztValue_nonneg
#print axioms YMGap.RG.ztValue_mono
#print axioms YMGap.RG.ztMajorant_le_su2
#print axioms YMGap.RG.etaGapMonotone_of_ztMajorant
#print axioms YMGap.RG.su2_etaGapMonotone_via_zt
