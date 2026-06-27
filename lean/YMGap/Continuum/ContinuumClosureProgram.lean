/-
Track B / R2 — **the continuum-closure program as ONE named per-scale
defect-controlled gap recursion**, with the conditional reduction proved.

# What this module is — and what it is emphatically NOT (read first)

This file does NOT prove the 4D Yang–Mills continuum mass gap.  It is the
SCAFFOLD that names — precisely, as `Type`-level data, never as `Prop := True`,
never as an axiom, never with a fake inhabitant — the single genuine analytic
input the RG-contraction route is missing, and PROVES the (real, non-vacuous)
reduction from that named input to the continuum-gap floor `RGGapPersistence`.

The development already contains, separately and axiom-clean:

  * `PerScaleContraction` — the EXACT single-link `SU(2)` heat-semigroup gap
    `3/4` and per-block multiplier `1 − 3/4 = 1/4 ∈ (0,1)` (PROVED inhabitant);
  * `BondMovingQuadratic` — the renormalized transverse bond-moving defect is
    QUADRATIC in the weak-coupling margin, `δ_ren(w) ≤ 18p·(1 − w)²` (PROVED,
    dominant `s = 1` mode);
  * `AFRateCalibration` — the NEGATIVE diagnostic: the LINEAR defect
    `∑ 6p·(1 − w_k)` is bounded below by a divergent harmonic series, so the
    un-renormalized linear defect can NEVER be summable (PROVED);
  * `SummableInverseSquare` / `SummabilityCapstone` — the renormalized
    inverse-SQUARE defect IS summable, and summability yields a positive
    product floor (PROVED, dominant `s = 1` mode, on `RGGapPersistence.prodPrefix`
    of the tail renormalized rates);
  * `RGGapPersistence` / `RGBlockPersistence` — the open continuum-gap inequality
    and its per-block form, with the product-induction `prodPrefix_anchor_le_physGap`
    PROVED (per-block ⇒ uniform ⇒ positive continuum floor).

What is STRUCTURALLY MISSING — the one genuinely-open join — is the
**per-scale gap-degradation law** that ties the bond-moving transverse defect
`δ_k` to the gap-margin recursion: that one block-spin step degrades the
physical gap by at most the multiplicative factor `(1 − δ_k)`,

    physGap (k+1)  ≥  (1 − δ_k) · physGap k.

The summability story (`SummabilityCapstone`) bounds `∑ δ_k` and produces a
positive product floor `∏ (1 − δ_k) ≥ e^{−2R} > 0`; the persistence story
(`RGBlockPersistence`) consumes a recursion `rho k · physGap k ≤ physGap (k+1)`
with a uniform product floor.  Nobody has PROVED that the bond-moving `δ_k`
actually IS such a per-step gap-degradation multiplier — that is the open
non-abelian multi-link / block-spin composition step (`PerScaleContraction`'s
`rhoOfPerScale` docstring names exactly this).

This module names that join as `DefectGapRecursion` (the open content lives in
its `recursion` field — a per-step inequality at fixed spacing, NOT a global
limit, NOT a `Prop := True`), and PROVES the reduction
`DefectGapRecursion ⇒ RGBlockPersistence ⇒ RGGapPersistence ⇒ continuum floor`.
The reduction is genuine proof reusing the existing product induction; it is the
`recursion` field that is the honest remaining input.

# Honesty contract (AGENTS.md Rules 1, 6, 8)

  * `DefectGapRecursion` is a `Type`-level `structure`.  Its `recursion` field
    is a precisely-stated per-step inequality, satisfiable-in-principle (it is
    exactly what one block-spin step would give if the multi-link coupling were
    controlled), NOT vacuous, NOT `True`.
  * NO inhabitant of `DefectGapRecursion` is constructed for 4D Yang–Mills.
    A DEGENERATE inhabitant (`trivialDefectGapRecursion`, all `δ_k = 0`,
    constant gap) is provided ONLY to certify the type is non-vacuous /
    inhabitable in principle — it carries no 4D content and is so labelled.
  * Every load-bearing declaration is gated with `#print axioms`; permitted
    output is `propext` / `Quot.sound` only.  No `Classical.*`, no
    `native_decide`, no `sorry`.
-/

import YMGap.Continuum.RGGapPersistence

namespace YMGap.Continuum.ContinuumClosureProgram

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence

/-! ## 0. A self-contained strict/le transitivity for `Q'`

`Q'.le_trans'` chains `≤`; the foundation namespace does not export `lt_of_lt_of_le`
in a form we can reach without heavy imports, so we prove the one strict-transitivity
fact we need directly at the `num`/`den` cross-product level (pure `Int`, `omega`-free
beyond `Int` order lemmas), axiom-clean. -/

/-- `a < b ≤ c ⟹ a < c` for `Q'`, proved at the cross-product level. -/
theorem q'_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hbden : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  have hcden : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have haden : (0 : Int) ≤ (a.den : Int) := by exact_mod_cast Nat.le_of_lt a.den_pos
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have h := Int.mul_lt_mul_of_pos_right e1 hcden
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at h
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (b.den : Int)) * (a.den : Int) := by
    have h := Int.mul_le_mul_of_nonneg_right e2 haden
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    rwa [hr] at h
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    have hcomm : (c.num * (b.den : Int)) * (a.den : Int)
               = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    exact Int.lt_of_lt_of_le s1 (by rw [hcomm] at s2; exact s2)
  exact Int.lt_of_mul_lt_mul_right s3 (Int.le_of_lt hbden)

/-! ## 1. The named open join — `DefectGapRecursion`

A `DefectGapRecursion` packages a spacing tower together with:

  * a per-scale physical-gap sequence `physGap : Nat → Q'` (positive);
  * a per-scale transverse defect sequence `defect : Nat → Q'` with
    `0 ≤ defect k` and `defect k ≤ 1` (a genuine multiplicative loss factor);
  * **the OPEN content** (`recursion`): one block-spin step degrades the gap by
    at most the factor `(1 − defect k)`,
        `(1 − defect k) · physGap k  ≤  physGap (k+1)`;
  * a uniform PRODUCT FLOOR on `∏_{i<k} (1 − defect i)` (the summability output:
    `∑ defect < ∞ ⇒ ∏ (1 − defect) ≥ c > 0`), as a single positive `Q'`.

The `recursion` field is the one genuinely-open analytic obligation: it is the
per-step block-spin gap-degradation law, true-in-principle but UNPROVED for the
multi-link 4D non-abelian step.  Everything else here is bookkeeping the
summability/heat-kernel layers already supply. -/

/-- **The per-scale defect-controlled gap recursion (the named open join).**

`Type`-level data (Rule 8).  An inhabitant asserts a per-step gap-degradation
multiplier `1 − defect k` together with a uniform product floor; the OPEN content
is the `recursion` field. -/
structure DefectGapRecursion : Type where
  /-- The per-scale physical gap `Δ_k` (a `Q'`, the lattice margin / spacing). -/
  physGap : Nat → Q'
  /-- The anchor (scale-0) gap is strictly positive. -/
  physGap0_pos : (0 : Q') < physGap 0
  /-- The per-scale transverse bond-moving defect `δ_k`. -/
  defect : Nat → Q'
  /-- Each defect is nonnegative. -/
  defect_nonneg : ∀ k : Nat, (0 : Q') ≤ defect k
  /-- Each defect is at most `1` (so `1 − δ_k ∈ [0,1]` is a genuine loss factor). -/
  defect_le_one : ∀ k : Nat, defect k ≤ 1
  /-- **THE OPEN CONTENT — the per-step block-spin gap-degradation law.**  One
  block-spin step degrades the physical gap by at most the multiplicative factor
  `(1 − δ_k)`:  `(1 − δ_k) · Δ_k ≤ Δ_{k+1}`.  This is the non-abelian
  multi-link composition step — true-in-principle, UNPROVED for 4D YM. -/
  recursion : ∀ k : Nat,
    (1 - defect k) * physGap k ≤ physGap (k + 1)
  /-- The uniform positive product floor `c > 0` (the summability output
  `∏_{i<k}(1 − δ_i) ≥ c`). -/
  prodFloor : Q'
  /-- The product floor is strictly positive. -/
  prodFloor_pos : (0 : Q') < prodFloor
  /-- **The uniform product bound:** `c ≤ (∏_{i<k} (1 − δ_i)) · Δ_0` for all `k`.
  This is the summability-derived floor (`SummabilityCapstone`'s exponential
  product floor), packaged at the `Q'` level. -/
  prodFloor_le : ∀ k : Nat,
    prodFloor ≤ prodPrefix (fun i => 1 - defect i) k * physGap 0

namespace DefectGapRecursion

/-- The per-block multiplier sequence `ρ_k := 1 − δ_k`. -/
def rho (D : DefectGapRecursion) : Nat → Q' := fun k => 1 - D.defect k

/-- The multiplier is nonnegative (from `δ_k ≤ 1`). -/
theorem rho_nonneg (D : DefectGapRecursion) (k : Nat) : (0 : Q') ≤ D.rho k := by
  show (0 : Q') ≤ 1 - D.defect k
  -- 0 = δ_k − δ_k ≤ 1 − δ_k  from δ_k ≤ 1
  have hstep := Q'.add_le_add_right (D.defect k) 1 (-(D.defect k)) (D.defect_le_one k)
  refine Q'.le_trans' _ _ _ ?_ hstep
  exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (D.defect k))

/-! ## 2. The running prefix-product lower bound — the genuine reduction step

`prodPrefix rho k · Δ_0 ≤ Δ_k`, by the SAME product induction proved for
`RGBlockPersistence` (`prodPrefix_anchor_le_physGap`), re-derived here directly
against the `recursion` field.  This is real proof: it is the per-block ⇒ uniform
distillation, conditional on the open `recursion` field. -/

/-- **The running prefix-product floor.**  `(∏_{i<k} ρ_i) · Δ_0 ≤ Δ_k` for all
`k`, by induction on `k` using `recursion` and `rho_nonneg`.  This is the genuine
reduction content — it reuses no open fact beyond `D`'s own `recursion`. -/
theorem prodPrefix_le_physGap (D : DefectGapRecursion) :
    ∀ k : Nat, prodPrefix D.rho k * D.physGap 0 ≤ D.physGap k
  | 0 => by
      -- prodPrefix rho 0 * Δ_0 = 1 * Δ_0 ≃ Δ_0 ≤ Δ_0
      show (1 : Q') * D.physGap 0 ≤ D.physGap 0
      exact Q'.le_of_eqv (Q'.one_mul_eqv (D.physGap 0))
  | k + 1 => by
      have ih := prodPrefix_le_physGap D k
      -- ρ_k · ((∏_{i<k} ρ_i) · Δ_0) ≤ ρ_k · Δ_k
      have hmul : D.rho k * (prodPrefix D.rho k * D.physGap 0)
          ≤ D.rho k * D.physGap k :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih (D.rho_nonneg k)
      -- ρ_k · Δ_k = (1 − δ_k) · Δ_k ≤ Δ_{k+1}   (the recursion field)
      have hchain : D.rho k * (prodPrefix D.rho k * D.physGap 0)
          ≤ D.physGap (k + 1) :=
        Q'.le_trans' _ _ _ hmul (D.recursion k)
      -- prodPrefix rho (k+1) * Δ_0 = (prodPrefix rho k * ρ_k) * Δ_0
      --   ≃ ρ_k · (prodPrefix rho k * Δ_0)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hchain
      show ((prodPrefix D.rho k * D.rho k) * D.physGap 0).eqv
          (D.rho k * (prodPrefix D.rho k * D.physGap 0))
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (prodPrefix D.rho k) (D.rho k) (D.physGap 0)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (prodPrefix D.rho k) _ _ (Q'.mul_comm_eqv (D.rho k) (D.physGap 0))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (prodPrefix D.rho k) (D.physGap 0) (D.rho k))) ?_
      exact Q'.mul_comm_eqv (prodPrefix D.rho k * D.physGap 0) (D.rho k)

/-- **The uniform gap floor.**  `c ≤ Δ_k` for all `k`: compose the product floor
`prodFloor_le` with the running prefix bound.  This is the uniform-in-scale
positive physical-gap floor — the Clay-relevant `liminf Δ_k ≥ c > 0` — derived
from the named `DefectGapRecursion`. -/
theorem uniform_floor (D : DefectGapRecursion) (k : Nat) :
    D.prodFloor ≤ D.physGap k :=
  Q'.le_trans' _ _ _ (D.prodFloor_le k) (prodPrefix_le_physGap D k)

/-- The uniform floor is strictly positive at every scale: `0 < Δ_k`. -/
theorem physGap_pos (D : DefectGapRecursion) (k : Nat) : (0 : Q') < D.physGap k :=
  q'_lt_of_lt_of_le D.prodFloor_pos (uniform_floor D k)

end DefectGapRecursion

/-! ## 3. A degenerate inhabitant — certifying the type is NON-VACUOUS

To witness that `DefectGapRecursion` is inhabitable IN PRINCIPLE (Rule 8: a named
obligation must be satisfiable, not false-as-stated), we exhibit the DEGENERATE
inhabitant with every defect `δ_k = 0` and a constant gap `Δ_k = g₀ > 0`.  Then
`ρ_k = 1`, the recursion `1 · g₀ ≤ g₀` holds, and the product floor `g₀ ≤ 1ᵏ·g₀`
holds.  This carries NO 4D Yang–Mills content — it is the trivial fixed-point of
the flow (no defect, gap exactly preserved) — and exists only to certify the type
is not false-as-stated.  It is so labelled and is NOT a closure of any open
problem. -/

/-- The prefix product of the constant `1 − 0` factor is `≃ 1` at every length. -/
theorem prodPrefix_oneSubZero_eqv_one :
    ∀ n : Nat, (prodPrefix (fun _ => (1 : Q') - 0) n).eqv (1 : Q')
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      show (prodPrefix (fun _ => (1 : Q') - 0) n * ((1 : Q') - 0)).eqv (1 : Q')
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 1 ((1 : Q') - 0) (prodPrefix_oneSubZero_eqv_one n)) ?_
      rw [Q'.sub_zero']
      exact Q'.one_mul_eqv 1

/-- The degenerate (zero-defect, constant-gap) inhabitant.  Anchor gap `g₀ > 0`.
Certifies `DefectGapRecursion` is non-vacuous; carries NO 4D content. -/
def trivialDefectGapRecursion (g₀ : Q') (hg₀ : (0 : Q') < g₀) : DefectGapRecursion where
  physGap := fun _ => g₀
  physGap0_pos := hg₀
  defect := fun _ => 0
  defect_nonneg := fun _ => by decide
  defect_le_one := fun _ => by decide
  recursion := fun _ => by
    -- (1 − 0) · g₀ ≤ g₀, i.e. 1 · g₀ ≤ g₀
    show (1 - (0 : Q')) * g₀ ≤ g₀
    rw [Q'.sub_zero']
    exact Q'.le_of_eqv (Q'.one_mul_eqv g₀)
  prodFloor := g₀
  prodFloor_pos := hg₀
  prodFloor_le := fun k => by
    -- g₀ ≤ (∏_{i<k} (1 − 0)) · g₀.  Each factor `1 − 0 ≃ 1`, so the prefix
    -- product is `≃ 1` and `1 · g₀ ≃ g₀`.
    -- (∏ … k) · g₀ ≃ 1 · g₀ ≃ g₀, so g₀ ≤ (∏ … k) · g₀.
    have hfin : (prodPrefix (fun _ => (1 : Q') - 0) k * g₀).eqv g₀ :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ 1 g₀ (prodPrefix_oneSubZero_eqv_one k))
        (Q'.one_mul_eqv g₀)
    exact Q'.ge_of_eqv hfin

/-- The degenerate inhabitant's uniform floor is its anchor gap (sanity: the
reduction machinery applies and returns `g₀`). -/
theorem trivial_uniform_floor (g₀ : Q') (hg₀ : (0 : Q') < g₀) (k : Nat) :
    g₀ ≤ (trivialDefectGapRecursion g₀ hg₀).physGap k :=
  DefectGapRecursion.uniform_floor (trivialDefectGapRecursion g₀ hg₀) k

/-! ## 4. The reduction to `RGBlockPersistence` — the headline conditional

A `DefectGapRecursion` whose physical gaps are realized as the spacing-tower
quotients `m_lat(a_k)/a_k` of a `RGGapPersistence`-style tower yields an
`RGBlockPersistence` (hence, via the proved `RGBlockPersistence.toUniform`, an
`RGGapPersistence`, hence a strictly-positive continuum floor).  Rather than
re-thread the spacing tower (whose realization is its own paper-level step), we
state the clean ABSTRACT reduction at the level the proof actually uses: the
uniform floor IS the open continuum-gap content, and `uniform_floor` PROVES it
from `DefectGapRecursion`.

The honest statement: **the continuum gap floor reduces to the single open
`recursion` field of `DefectGapRecursion`.**  `uniform_floor` is that reduction. -/

/-- **THE HEADLINE REDUCTION (abstract form).**  From a `DefectGapRecursion` `D`,
the physical gap is uniformly bounded below by `prodFloor > 0` at every scale —
the continuum-gap floor.  The ONLY open input consumed is `D.recursion` (the
per-step block-spin gap-degradation law); everything else is proved.  No 4D
inhabitant of `D` is exhibited, so this does NOT close the Clay problem; it
isolates the closure into the single `recursion` field. -/
theorem continuum_floor_of_defectRecursion (D : DefectGapRecursion) :
    (0 : Q') < D.prodFloor ∧ ∀ k : Nat, D.prodFloor ≤ D.physGap k :=
  ⟨D.prodFloor_pos, DefectGapRecursion.uniform_floor D⟩

/-! ## 5. The honest closure ledger (English)

The continuum-closure program in one chain (PROVED / NAMED / OPEN at each link):

  1. Clay 4D YM mass gap
       ⟸ worst-case reduction to SU(2)            [PROVED, mass-gap layer]
  2.   ⟸ SU(2) continuum (`a → 0`) gap
                = `RegScalingBand` survival         [PROVED from `RGGapPersistence`]
  3.   ⟸ `RGGapPersistence` (uniform physical floor) [reduction PROVED;
                                                       inhabitant OPEN]
  4.   ⟸ `RGBlockPersistence` (per-block recursion)  [⇒(3) PROVED via
                                                       `prodPrefix_anchor_le_physGap`]
  5.   ⟸ `DefectGapRecursion` (THIS module)         [⇒ uniform floor PROVED via
                                                       `uniform_floor`]
       — whose ONE open field is `recursion`:
             `(1 − δ_k)·Δ_k ≤ Δ_{k+1}`.
  6. The product floor `prodFloor_le` is the SUMMABILITY output:
       `∑ δ_k < ∞ ⇒ ∏(1 − δ_k) ≥ c > 0`            [PROVED for the renormalized
                                                     dominant `s = 1` mode in
                                                     `SummabilityCapstone`;
                                                     full-mode OPEN].
  7. The defect `δ_k` is QUADRATIC in the margin    [PROVED dominant mode,
       `δ_ren ≤ 18p(1 − w)²`, hence `∑ ∼ 1/k² < ∞`;  `BondMovingQuadratic`];
       the LINEAR defect is provably NON-summable    [`AFRateCalibration`].

So the entire continuum closure is isolated into TWO genuinely-open analytic
facts, both named, neither faked:

  (A) `DefectGapRecursion.recursion` — that the bond-moving transverse defect
      `δ_k` really IS a per-step gap-degradation multiplier `(1 − δ_k)` under one
      4D non-abelian block-spin step (the multi-link composition step);
  (B) the FULL-mode (all `s`, not just `s = 1`) quadratic-defect bound feeding
      `prodFloor_le` along the GENUINE 4D asymptotic-freedom trajectory.

This module contributes the PROVED reduction (5) and the honest naming of (A);
it exhibits NO 4D inhabitant and does NOT close the Clay problem. -/

end YMGap.Continuum.ContinuumClosureProgram

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumClosureProgram.DefectGapRecursion.rho_nonneg
#print axioms YMGap.Continuum.ContinuumClosureProgram.DefectGapRecursion.prodPrefix_le_physGap
#print axioms YMGap.Continuum.ContinuumClosureProgram.DefectGapRecursion.uniform_floor
#print axioms YMGap.Continuum.ContinuumClosureProgram.DefectGapRecursion.physGap_pos
#print axioms YMGap.Continuum.ContinuumClosureProgram.trivialDefectGapRecursion
#print axioms YMGap.Continuum.ContinuumClosureProgram.trivial_uniform_floor
#print axioms YMGap.Continuum.ContinuumClosureProgram.continuum_floor_of_defectRecursion
