/-
Track B / R2 — **a GENUINE partial inhabitant of the canonical spacing-uniform
floor, on a BOUNDED / FINITE spacing window.**

# Why this module exists (read first — and the HONEST scope)

`UniformSpacingFloor le g` is the single open continuum input: ONE strictly-
positive rational `floor` lying below a per-scale gap quantity `g i` UNIFORMLY at
EVERY scale `i` at once.  It is uninhabited for the genuine `a → 0` continuum,
because the uniformity must survive arbitrarily fine spacing.

But the FIXED-SPACING gap IS proven in this development: at each fixed scale the
finite (compact) transfer operator carries a `LocatedSpectralGap`, whose
`gapMargin = 1 − sep > 0` is a strictly-positive `Q'` quantity
(`LocatedSpectralGap.gapMargin_pos`), and the concrete `constGappedLocated`
family realizes this with the proven `sep = 1/2` gap, margin `1/2`.

This module turns those per-scale positive gaps into a GENUINE inhabitant of a
WINDOWED floor:

  * **`WindowedUniformSpacingFloor le g M`** — the same canonical interface, but
    the `bound` ranges only over the finite window `{N | N ≤ M}`.
  * **`finMin`** — the minimum of the finitely-many per-scale gaps over a window.
    `finMin_pos` (a min of positives is positive) and `finMin_le` (the min lies
    below each windowed entry) are proved by elementary `Q'`-order induction.
  * **`windowedFloorOfPos`** — from ANY per-scale strictly-positive `g : Nat → Q'`
    it builds `WindowedQFloor g M`.  This GENUINELY inhabits the windowed floor.
  * **concrete numeric inhabitant** — `concreteWindowFloor M` instantiates this at
    the proven `constGappedLocated` `gapMargin` family (every entry `= 1/2`), and
    `concrete_windowed_gap` drives a windowed analog of the unification capstone:
    one shared floor below the per-scale CReal gap AND the per-scale `Q'` gap on
    the whole window `{0,…,M}` at once.

# HONESTY — this is a WINDOW, the `a → 0` floor is still open

The windowed floor is a real, fully-inhabited Type-level object — but it is NOT
the open input.  The honest residual is exactly the **degradation as `M → ∞`**:

  * `finMin` is a min over MORE scales as the window grows, so it can only shrink.
  * For a per-scale gap that genuinely degrades with the scale — `Q'.invSucc`,
    `g N = 1/(N+1)` — `windowedFloor_invSucc` inhabits `WindowedQFloor invSucc M`
    for EVERY `M`, yet `windowFloor_invSucc_le` shows its floor is `≤ 1/(M+1) → 0`,
    and `no_full_floor_invSucc` proves the FULL (all-`N`) `QFloor invSucc` is
    CONTRADICTORY: no strictly-positive rational sits below `1/(N+1)` for all `N`.

That is the precise shape of the open `a → 0` physics: the proven fixed-spacing
gaps give a windowed floor at every finite `M`, but the uniform-over-ALL-scales
floor — `UniformSpacingFloor` itself — is exactly what survives only if the
per-scale gaps do NOT degrade to `0` along the scaling schedule.  Nothing here
fakes that; the constant `constGappedLocated` family is the degenerate
volume-independent placeholder, and its (non-degrading) full floor is no continuum
proof.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

All carriers are `Type`-level data (the windowed `bound` is a `Pi` over the order
relation, never a `Prop`-∃).  Order facts go through `Int` core arithmetic and
`omega`; no `Classical.*`, no `by_cases`, no `native_decide`, no `sorry`.  Each
load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.UnifiedContinuumFloor
import YMGap.Continuum.ContinuumGapLimit
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.WindowedSpacingFloor

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.UnifiedContinuumFloor
open YMGap.Continuum.ContinuumGapLimit
open YMGap.Continuum.LocatedSpectralGap

/-! ## 1. `Q'`-order helper lemmas for the finite minimum

`Q'.min' p q = if p ≤ q then p else q`.  The two projection inequalities and the
strict-positivity preservation are all the order content `finMin` needs; each is a
`split` of the decidable `if` plus core `Int` order. -/

/-- `min' p q ≤ p` (the left projection of the located min). -/
theorem min'_le_left (p q : Q') : Q'.min' p q ≤ p := by
  unfold Q'.min'
  split
  · exact Q'.le_refl' p
  · rename_i h
    show q.num * (p.den : Int) ≤ p.num * (q.den : Int)
    exact Int.le_of_lt (Int.not_le.mp h)

/-- `min' p q ≤ q` (the right projection of the located min). -/
theorem min'_le_right (p q : Q') : Q'.min' p q ≤ q := by
  unfold Q'.min'
  split
  · rename_i h; exact h
  · exact Q'.le_refl' q

/-- A min of two strictly-positive rationals is strictly positive. -/
theorem min'_pos {p q : Q'} (hp : (0 : Q') < p) (hq : (0 : Q') < q) :
    (0 : Q') < Q'.min' p q := by
  unfold Q'.min'
  split
  · exact hp
  · exact hq

/-! ## 2. The finite minimum over a window `{0,…,M}` and its two laws -/

/-- `finMin g M` = the minimum of `g 0, …, g M`, the windowed floor of a per-scale
`Q'` gap family. -/
def finMin (g : Nat → Q') : Nat → Q'
  | 0 => g 0
  | (M + 1) => Q'.min' (g (M + 1)) (finMin g M)

/-- **The windowed min is strictly positive** when every per-scale gap is. -/
theorem finMin_pos (g : Nat → Q') (hpos : ∀ N, (0 : Q') < g N) :
    ∀ M, (0 : Q') < finMin g M
  | 0 => hpos 0
  | (M + 1) => min'_pos (hpos (M + 1)) (finMin_pos g hpos M)

/-- **The windowed min lies below every windowed entry**: `finMin g M ≤ g N` for
all `N ≤ M`.  This is the uniform-over-the-window floor property. -/
theorem finMin_le (g : Nat → Q') : ∀ M N, N ≤ M → finMin g M ≤ g N
  | 0, N, hN => by
      have hN0 : N = 0 := Nat.le_zero.mp hN
      subst hN0
      exact Q'.le_refl' (g 0)
  | (M + 1), N, hN => by
      rcases Nat.lt_or_ge N (M + 1) with hlt | hge
      · have hNM : N ≤ M := Nat.lt_succ_iff.mp hlt
        show Q'.min' (g (M + 1)) (finMin g M) ≤ g N
        exact Q'.le_trans' _ _ _ (min'_le_right (g (M + 1)) (finMin g M))
          (finMin_le g M N hNM)
      · have heq : N = M + 1 := Nat.le_antisymm hN hge
        subst heq
        show Q'.min' (g (M + 1)) (finMin g M) ≤ g (M + 1)
        exact min'_le_left (g (M + 1)) (finMin g M)

/-! ## 3. The windowed floor interface — `UniformSpacingFloor` over a finite window

Same canonical shape as `UniformSpacingFloor`, but the `bound` ranges only over
`{N | N ≤ M}`.  All data is `Type`-level (Rule 8): `bound` is a `Pi` of the order
relation, never a `Prop`-∃. -/

/-- **THE WINDOWED SPACING-UNIFORM FLOOR.**  A strictly-positive rational `floor`
lying — via `le` — below the per-scale gap quantity `g N` for every scale `N ≤ M`.
Unlike `UniformSpacingFloor`, this is GENUINELY inhabited (from the proven per-
scale gaps); the open content is recovered only in the `M → ∞` limit. -/
structure WindowedUniformSpacingFloor {α : Type} (le : Q' → α → Prop)
    (g : Nat → α) (M : Nat) : Type where
  /-- The windowed positive floor. -/
  floor : Q'
  /-- The floor is strictly positive. -/
  floor_pos : (0 : Q') < floor
  /-- The floor lies below the per-scale gap quantity at every scale in the
  window `{N | N ≤ M}`. -/
  bound : ∀ N, N ≤ M → le floor (g N)

/-- `Q'`-valued windowed floor (plain rational order). -/
abbrev WindowedQFloor (g : Nat → Q') (M : Nat) : Type :=
  WindowedUniformSpacingFloor (fun (q x : Q') => q ≤ x) g M

/-- `CReal`-valued windowed floor (eventual order on `ofQ'`). -/
abbrev WindowedCRealFloor (g : Nat → CReal) (M : Nat) : Type :=
  WindowedUniformSpacingFloor
    (fun (q : Q') (x : CReal) => CReal.leEv (CReal.ofQ' q) x) g M

/-! ## 4. The inhabitation theorem — proven per-scale gaps ⇒ windowed floor

This is the genuine partial-inhabitant result: ANY per-scale strictly-positive
`Q'` gap family yields a windowed floor at the finite min, for every window. -/

/-- **WINDOWED FLOOR INHABITED.**  From a per-scale strictly-positive gap family
`g : Nat → Q'` (with `∀ N, 0 < g N`) the finite minimum `finMin g M` is a genuine
`WindowedQFloor g M`. -/
def windowedFloorOfPos (g : Nat → Q') (hpos : ∀ N, (0 : Q') < g N) (M : Nat) :
    WindowedQFloor g M where
  floor := finMin g M
  floor_pos := finMin_pos g hpos M
  bound := fun N hN => finMin_le g M N hN

/-- A full `QFloor` restricts to a `WindowedQFloor` on any window (the easy
direction; the converse is the open/degrading content). -/
def restrictQToWindow {g : Nat → Q'} (M : Nat) (F : QFloor g) :
    WindowedQFloor g M where
  floor := F.floor
  floor_pos := F.floor_pos
  bound := fun N _ => F.bound N

/-- A full `CRealFloor` restricts to a `WindowedCRealFloor` on any window. -/
def restrictCRealToWindow {g : Nat → CReal} (M : Nat) (F : CRealFloor g) :
    WindowedCRealFloor g M where
  floor := F.floor
  floor_pos := F.floor_pos
  bound := fun N _ => F.bound N

/-! ## 5. Windowed unification capstone — one shared floor, both per-scale routes

The honest windowed analog of `unified_continuum_gap`: a SINGLE shared positive
floor (presented as a windowed CReal floor `cod` and a windowed `Q'` floor `cur`,
tied by `hshared`) lies below the per-scale CReal gap AND the per-scale `Q'` gap
across the whole window `{0,…,M}`.  No continuum-residual is assembled — that needs
the all-`N` floor, which is the open input. -/

/-- **WINDOWED UNIFICATION CAPSTONE.**  One shared floor (`cur.floor = cod.floor`)
yields, on the whole window `{N | N ≤ M}`: its strict positivity, the per-scale
CReal-gap bound `ofQ' cur.floor ≤ g N`, and the per-scale `Q'`-gap bound
`cur.floor ≤ h N`. -/
theorem windowed_unified_continuum_gap {g : Nat → CReal} {h : Nat → Q'} {M : Nat}
    (cod : WindowedCRealFloor g M) (cur : WindowedQFloor h M)
    (hshared : cod.floor = cur.floor) :
    ( (0 : Q') < cur.floor
        ∧ ∀ N, N ≤ M → CReal.leEv (CReal.ofQ' cur.floor) (g N) )
    ∧ ( ∀ N, N ≤ M → cur.floor ≤ h N ) := by
  refine ⟨⟨cur.floor_pos, ?_⟩, cur.bound⟩
  intro N hN
  have hb := cod.bound N hN
  rw [hshared] at hb
  exact hb

/-! ## 6. Concrete numeric inhabitant — the proven `constGappedLocated` gap (1/2)

`constGappedLocated N` is the proven `sep = 1/2` located gap at every scale, with
strictly-positive margin `gapMargin = 1/2` (`gapMargin_pos`).  We window it. -/

/-- The proven per-scale `Q'` gap: the located gap margin `1 − sep = 1/2` of the
concrete `constGappedLocated` family. -/
def constGappedGap (N : Nat) : Q' := (constGappedLocated N).gapMargin

/-- Each per-scale gap is strictly positive — the proven fixed-spacing gap. -/
theorem constGappedGap_pos (N : Nat) : (0 : Q') < constGappedGap N :=
  (constGappedLocated N).gapMargin_pos

/-- Each per-scale gap meets the proven mass floor `1/2 ≤ gapMargin`
(`constGapped_uniform_floor`) — the gaps are exactly the `1/2` mass scale. -/
theorem constGappedGap_ge_half (N : Nat) :
    Q'.mkPos 1 2 (by decide) ≤ constGappedGap N :=
  constGapped_uniform_floor N

/-- The concrete windowed `Q'` floor at the proven `constGappedLocated` gaps. -/
def concreteWindowFloor (M : Nat) : WindowedQFloor constGappedGap M :=
  windowedFloorOfPos constGappedGap constGappedGap_pos M

/-- The concrete windowed `CReal` floor at the lifted proven gaps, sharing the
same scalar floor as `concreteWindowFloor`. -/
def concreteWindowCReal (M : Nat) :
    WindowedCRealFloor (fun N => CReal.ofQ' (constGappedGap N)) M where
  floor := finMin constGappedGap M
  floor_pos := finMin_pos constGappedGap constGappedGap_pos M
  bound := fun N hN =>
    CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (finMin_le constGappedGap M N hN))

/-- **CONCRETE WINDOWED MASS GAP.**  At the proven `constGappedLocated` family, the
single windowed floor sits — across the whole window `{0,…,M}` — below the per-
scale CReal gap and the per-scale `Q'` gap simultaneously; it is strictly positive.
A genuine, fully-inhabited windowed instance of the unification capstone. -/
theorem concrete_windowed_gap (M : Nat) :
    ( (0 : Q') < (concreteWindowFloor M).floor
        ∧ ∀ N, N ≤ M → CReal.leEv (CReal.ofQ' (concreteWindowFloor M).floor)
            (CReal.ofQ' (constGappedGap N)) )
    ∧ ( ∀ N, N ≤ M → (concreteWindowFloor M).floor ≤ constGappedGap N ) :=
  windowed_unified_continuum_gap (concreteWindowCReal M) (concreteWindowFloor M) rfl

/-! ## 7. HONEST residual — the floor DEGRADES as `M → ∞`

For a per-scale gap that genuinely shrinks with the scale (`Q'.invSucc N = 1/(N+1)`,
the prototype of a degrading spacing-dependent gap), the windowed floor is
inhabited at EVERY finite `M`, yet its value is `≤ 1/(M+1) → 0`, and the FULL
(all-`N`) floor is contradictory.  This is exactly the open `a → 0` shape. -/

/-- The degrading per-scale gap `invSucc` admits a windowed floor for EVERY `M`. -/
def windowedFloor_invSucc (M : Nat) : WindowedQFloor Q'.invSucc M :=
  windowedFloorOfPos Q'.invSucc Q'.invSucc_pos M

/-- **DEGRADATION (quantitative).**  The windowed `invSucc` floor is `≤ 1/(M+1)`,
which tends to `0` as the window grows — the windowed floor is NOT uniform. -/
theorem windowFloor_invSucc_le (M : Nat) :
    (windowedFloor_invSucc M).floor ≤ Q'.invSucc M :=
  finMin_le Q'.invSucc M M (Nat.le_refl M)

/-- **NO UNIFORM FLOOR (the open residual, made precise).**  A FULL (all-`N`)
`QFloor` on the degrading family `invSucc` is CONTRADICTORY: no strictly-positive
rational `floor` can satisfy `floor ≤ 1/(N+1)` for every `N`.  Taking
`N = floor.den` forces `floor.num · (floor.den + 1) ≤ floor.den` with
`floor.num ≥ 1`, i.e. `floor.den + 1 ≤ floor.den`. -/
theorem no_full_floor_invSucc (F : QFloor Q'.invSucc) : False := by
  -- floor > 0 ⇒ its numerator is ≥ 1
  have hnum : (1 : Int) ≤ F.floor.num := by
    have h : (0 : Q').num * (F.floor.den : Int)
        < F.floor.num * ((0 : Q').den : Int) := F.floor_pos
    rw [show (0 : Q').num = 0 from rfl, show ((0 : Q').den : Int) = 1 from rfl] at h
    omega
  -- the all-N bound at the index N = floor.den
  have hb : F.floor.num * ((Q'.invSucc F.floor.den).den : Int)
      ≤ (Q'.invSucc F.floor.den).num * (F.floor.den : Int) := F.bound F.floor.den
  rw [Q'.invSucc_den, Q'.invSucc_num] at hb
  -- hb : floor.num * ↑(floor.den + 1) ≤ 1 * ↑floor.den
  have hsub : (F.floor.num - 1) * ((F.floor.den + 1 : Nat) : Int)
      = F.floor.num * ((F.floor.den + 1 : Nat) : Int)
        - ((F.floor.den + 1 : Nat) : Int) := by
    rw [Int.sub_mul, Int.one_mul]
  have h3 : (0 : Int) ≤ (F.floor.num - 1) * ((F.floor.den + 1 : Nat) : Int) :=
    Int.mul_nonneg (by omega) (by omega)
  rw [hsub] at h3
  omega

end YMGap.Continuum.WindowedSpacingFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WindowedSpacingFloor.min'_le_left
#print axioms YMGap.Continuum.WindowedSpacingFloor.min'_le_right
#print axioms YMGap.Continuum.WindowedSpacingFloor.min'_pos
#print axioms YMGap.Continuum.WindowedSpacingFloor.finMin_pos
#print axioms YMGap.Continuum.WindowedSpacingFloor.finMin_le
#print axioms YMGap.Continuum.WindowedSpacingFloor.windowedFloorOfPos
#print axioms YMGap.Continuum.WindowedSpacingFloor.restrictQToWindow
#print axioms YMGap.Continuum.WindowedSpacingFloor.restrictCRealToWindow
#print axioms YMGap.Continuum.WindowedSpacingFloor.windowed_unified_continuum_gap
#print axioms YMGap.Continuum.WindowedSpacingFloor.concreteWindowFloor
#print axioms YMGap.Continuum.WindowedSpacingFloor.concreteWindowCReal
#print axioms YMGap.Continuum.WindowedSpacingFloor.concrete_windowed_gap
#print axioms YMGap.Continuum.WindowedSpacingFloor.windowedFloor_invSucc
#print axioms YMGap.Continuum.WindowedSpacingFloor.windowFloor_invSucc_le
#print axioms YMGap.Continuum.WindowedSpacingFloor.no_full_floor_invSucc
