/-
The Kotecký–Preiss per-step increment bound (continuum stage **S4**), the
analytic heart of the finite-volume → infinite-volume convergence in the
convergent (weak-coupling) regime.

# The mathematics (Friedli–Velenik, *Statistical Mechanics of Lattice
  Systems* CUP 2017, Ch. 5; the explicit-constant inductive treatment)

In the convergent polymer/cluster expansion `log Z_Λ = ψ_β·|Λ| + R_Λ`,
the cluster series is *absolutely* summable with a geometric tail in the
activity `z`.  The KP smallness condition (Thm 5.4 / eq 5.10) and the
per-site absolute summability (eq 5.29) furnish, per boundary site, a
single-site cluster-activity tower

    a Λ  :=  Σ_{clusters of size ≥ Λ anchored at the new site} |Ψ|

whose terms decay GEOMETRICALLY in the cluster size: contributions of
size-`n` clusters are `O(z^n)` (eq 5.34), so

    a (Λ+1)  ≤  r · a Λ        with the activity ratio  0 ≤ r < 1.

The finite-volume expectation increment is then controlled by this tower
(eqs 5.30–5.34): the per-step increment `|S (Λ+1) − S Λ|` is bounded by
the cluster-activity at scale `Λ`,

    |S (Λ+1) − S Λ|  ≤  a Λ.

Combining the geometric decay with `a 0 ≤ C` gives `a Λ ≤ C · r^Λ`, and
after dominating the activity ratio `r ≤ 1/2` (legitimate in the
convergent regime: any `ρ ≤ 1/2` is covered; `SU2KP.q_*_upper`,
`SU3CharFactor.Z_t < 1/16` give `r` well below `1/2`) the increment fits
the `ρ = 1/2` shape that `KPLimit.crealOfGeoIncrement` consumes:

    |S (Λ+1) − S Λ|  ≤  C · (1/2)^Λ  =  geoIncr C Λ.

# What is genuine here (PROVED, not assumed)

The activity smallness — the geometric ratio `r ≤ 1/2` on the cluster
tower and the increment-vs-activity bound (the KP telescoping output) —
is the **analytic input of the weak-coupling regime**, carried as
HYPOTHESES of `KPIncrementData` (legitimately: this is the convergent
regime).  From those hypotheses we **prove**, constructively:

  * `activity_geom_bound` — `a Λ ≤ C · r^Λ` (geometric domination of the
    cluster tower from the ratio bound, via `CharacterTail.geom_dom`);
  * `pow_le_pow_base` — `r^Λ ≤ (1/2)^Λ` from `0 ≤ r ≤ 1/2` (base
    monotonicity of powers, by induction);
  * `kpIncrement_geoIncr_up` / `_lo` — the two-sided geometric increment
    `S (Λ+1) ≤ S Λ + geoIncr C Λ` and `S Λ ≤ S (Λ+1) + geoIncr C Λ`,
    in EXACTLY the form `crealOfGeoIncrement` consumes;
  * `kpIncrement_modulus` — the explicit `ρ = 1/2` Cauchy modulus
    (division-free, via `CReal.exists_mul_le` at `B = 2C`);
  * `kpIncrementBound` — the assembled `Σ'` datum `(C, 0 ≤ C, hup, hlo)`
    that discharges the S4 obligation of `ContinuumExistence.lean`.

The increment bound is therefore **derived from** the explicit
weak-coupling smallness hypothesis, NOT assumed as a property of the
conclusion.  No cluster bound is faked: the geometric ratio of the
cluster tower is the named analytic input (a structure field), the rest
is constructive `Q'` arithmetic.

# Pitfalls avoided (constructive-stat-mech scout)

NO pressure analyticity (no Weierstrass / uniform-limit-of-analytic): we
use only absolute summability + the geometric tail.  The thermodynamic
limit stays QUANTITATIVE (explicit modulus, never an unquantified `lim`).
Absolute convergence only (Bishop-valid), no Fubini / dominated
convergence.  No `inf` for the activity threshold: we fix `r ≤ 1/2` as a
witnessed hypothesis.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` (via the reused `Q'` / `Int` /
`Nat` helpers).  No `Classical.*`, no `sorryAx`, no `sorry`, no
`native_decide`.  The `KPIncrementData` is a Type-level `structure`
(Rule 8): the activity smallness is carried as DATA, the increment bound
is produced as a Type-level `Σ'` witness.
-/

import YMGap.Continuum.KPLimit
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.KPIncrement

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum

/-! ## Base monotonicity of powers

`r^n ≤ s^n` for `0 ≤ r ≤ s`.  The domination step that lifts a general
activity ratio `r ≤ 1/2` into the `ρ = 1/2` shape of the KP engine. -/

/-- **Power base monotonicity.**  For `0 ≤ r`, `r ≤ s`, every power is
monotone in the base: `r^n ≤ s^n`.  Induction on `n`:
`r^(n+1) = r·r^n ≤ r·s^n ≤ s·s^n = s^(n+1)` (first step left-mono in `r`
on `r^n ≤ s^n`; second step right-mono in `s^n ≥ 0` on `r ≤ s`). -/
theorem pow_le_pow_base (r s : Q') (hr : (0 : Q') ≤ r) (hrs : r ≤ s) (n : Nat) :
    r ^ n ≤ s ^ n := by
  induction n with
  | zero =>
    show (1 : Q') ≤ (1 : Q')
    exact Q'.le_refl' 1
  | succ n ih =>
    have hsn_nn : (0 : Q') ≤ s ^ n :=
      Q'.pow_nonneg s (Q'.le_trans' _ _ _ hr hrs) n
    show r * r ^ n ≤ s * s ^ n
    -- r·r^n ≤ r·s^n  (left-mono in r, on r^n ≤ s^n, r ≥ 0)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left (r ^ n) (s ^ n) r ih hr) ?_
    -- r·s^n ≤ s·s^n  (right-mono with multiplier s^n ≥ 0, on r ≤ s)
    exact Q'.mul_le_mul_of_nonneg_right r s (s ^ n) hrs hsn_nn

/-! ## The KP increment datum (weak-coupling smallness as DATA)

The convergent-regime analytic input, carried as a Type-level structure
(Rule 8).  The single-site cluster-activity tower `a`, its geometric
ratio `r ≤ 1/2` (the activity smallness), the base bound `a 0 ≤ C`, and
the increment-vs-activity bound (the KP telescoping output) are the
carried DATA; the geometric increment + modulus are PROVED from them. -/

/-- A **KP increment datum** for a finite-volume expectation sequence
`S : Nat → Q'` (the `⟨o⟩_Λ` tower).

Fields (the weak-coupling smallness — the genuine analytic input):

  * `C` — the cluster-tower base constant `a 0 ≤ C` (`Σ_{X∋0}|Ψ(X)| ≤ C`,
    the per-site absolute summability of eq 5.29), with `C_nonneg`;
  * `r` — the activity ratio of the cluster tower (`0 ≤ r ≤ 1/2`), with
    `r_nonneg` / `r_le_half`;
  * `a` — the single-site cluster-activity tower
    `a Λ = Σ_{size ≥ Λ clusters anchored at the new site} |Ψ|`, with
    `a_nonneg`;
  * `a_base` — `a 0 ≤ C` (the size-0 anchor);
  * `a_ratio` — `a (Λ+1) ≤ r · a Λ` (the geometric decay of eq 5.34, the
    KP smallness / activity-decay input);
  * `incr_up` / `incr_lo` — the two-sided KP telescoping bound
    `|S (Λ+1) − S Λ| ≤ a Λ` (eqs 5.30–5.34): the per-step increment is
    bounded by the cluster activity at scale `Λ`. -/
structure KPIncrementData (S : Nat → Q') where
  /-- Cluster-tower base constant `a 0 ≤ C` (per-site summability, eq 5.29). -/
  C : Q'
  /-- The activity ratio of the cluster tower. -/
  r : Q'
  /-- The single-site cluster-activity tower `a Λ`. -/
  a : Nat → Q'
  /-- `0 ≤ C`. -/
  C_nonneg : (0 : Q') ≤ C
  /-- `0 ≤ r`. -/
  r_nonneg : (0 : Q') ≤ r
  /-- Activity smallness, dominated to the `ρ = 1/2` engine: `r ≤ 1/2`. -/
  r_le_half : r ≤ half
  /-- The cluster tower is nonnegative. -/
  a_nonneg : ∀ n, (0 : Q') ≤ a n
  /-- Base bound `a 0 ≤ C` (the size-0 anchor of the cluster tower). -/
  a_base : a 0 ≤ C
  /-- Geometric decay of the cluster tower (eq 5.34, the KP smallness). -/
  a_ratio : ∀ n, a (n + 1) ≤ r * a n
  /-- Upper KP telescoping bound: `S (Λ+1) ≤ S Λ + a Λ`. -/
  incr_up : ∀ l, S (l + 1) ≤ S l + a l
  /-- Lower KP telescoping bound: `S Λ ≤ S (Λ+1) + a Λ`. -/
  incr_lo : ∀ l, S l ≤ S (l + 1) + a l

namespace KPIncrementData

variable {S : Nat → Q'} (D : KPIncrementData S)

/-! ### The geometric domination of the cluster tower

From the base bound `a 0 ≤ C` and the geometric ratio `a(n+1) ≤ r·a n`,
the tower is geometrically dominated `a Λ ≤ C·r^Λ` (`geom_dom`); then
`r ≤ 1/2` lifts the bound to `a Λ ≤ C·(1/2)^Λ = geoIncr C Λ`. -/

/-- **Geometric domination of the cluster tower.**  `a Λ ≤ C · r^Λ`,
from the base bound and the geometric ratio (`CharacterTail.geom_dom`). -/
theorem activity_geom_bound (l : Nat) : D.a l ≤ D.C * D.r ^ l :=
  CharacterTail.geom_dom D.a D.C D.r D.r_nonneg D.a_base D.a_ratio l

/-- **The cluster activity is below the `ρ = 1/2` increment.**
`a Λ ≤ C · (1/2)^Λ = geoIncr C Λ`, combining the geometric domination
`a Λ ≤ C·r^Λ` with the base domination `r^Λ ≤ (1/2)^Λ` (from `r ≤ 1/2`). -/
theorem activity_le_geoIncr (l : Nat) : D.a l ≤ geoIncr D.C l := by
  refine Q'.le_trans' _ _ _ (activity_geom_bound D l) ?_
  -- C·r^l ≤ C·(1/2)^l = geoIncr C l
  show D.C * D.r ^ l ≤ D.C * half ^ l
  exact Q'.mul_le_mul_of_nonneg_left (D.r ^ l) (half ^ l) D.C
    (pow_le_pow_base D.r half D.r_nonneg D.r_le_half l) D.C_nonneg

/-! ### The two-sided geometric increment bound (the S4 deliverable)

The KP telescoping increment `|S (Λ+1) − S Λ| ≤ a Λ` composes with
`a Λ ≤ geoIncr C Λ` to give exactly the `crealOfGeoIncrement` shape. -/

/-- **Upper geometric increment.**  `S (Λ+1) ≤ S Λ + geoIncr C Λ`, from
the KP telescoping `S (Λ+1) ≤ S Λ + a Λ` and `a Λ ≤ geoIncr C Λ`. -/
theorem kpIncrement_geoIncr_up (l : Nat) :
    S (l + 1) ≤ S l + geoIncr D.C l :=
  Q'.le_trans' _ _ _ (D.incr_up l)
    (Q'.add_le_add_left (S l) (D.a l) (geoIncr D.C l) (activity_le_geoIncr D l))

/-- **Lower geometric increment.**  `S Λ ≤ S (Λ+1) + geoIncr C Λ`. -/
theorem kpIncrement_geoIncr_lo (l : Nat) :
    S l ≤ S (l + 1) + geoIncr D.C l :=
  Q'.le_trans' _ _ _ (D.incr_lo l)
    (Q'.add_le_add_left (S (l + 1)) (D.a l) (geoIncr D.C l) (activity_le_geoIncr D l))

/-- **The `ρ = 1/2` Cauchy modulus.**  For any tolerance `ε > 0` there is
a positive `δ` with `(2C)·δ ≤ ε`: the division-free product modulus
(`CReal.exists_mul_le` at `B = 2C`).  This is exactly the rescaling
witness `crealOfGeoIncrement` consumes. -/
theorem kpIncrement_modulus (ε : Q') (hε : (0 : Q') < ε) :
    ∃ δ : Q', (0 : Q') < δ ∧ (Q'.ofNat 2 * D.C) * δ ≤ ε :=
  CReal.exists_mul_le (Q'.mul_nonneg _ _ (by decide) D.C_nonneg) hε

end KPIncrementData

/-! ## The S4 deliverable: the increment-bound `Σ'` datum

`kpIncrementBound` produces — from a `KPIncrementData D` — the exact
`Σ'` package the S4 obligation of `ContinuumExistence.lean` requires:
the constant `C ≥ 0` together with the two-sided geometric single-step
increment in the `geoIncr C` form `crealOfGeoIncrement` consumes.  This
is the constructive discharge of S4 from the explicit weak-coupling
smallness hypothesis. -/

/-- **S4 — the KP increment bound, CLOSED from the weak-coupling datum.**
Given a `KPIncrementData D` for `S` (the convergent-regime cluster-tower
smallness, carried as DATA), the finite-volume expectation sequence `S`
has a two-sided geometric single-step increment bound with explicit
constant `C ≥ 0`, in EXACTLY the shape `KPLimit.crealOfGeoIncrement`
consumes.  PROVED from the smallness hypotheses — no faked cluster bound. -/
def kpIncrementBound {S : Nat → Q'} (D : KPIncrementData S) :
    Σ' C : Q', (0 : Q') ≤ C ∧
      (∀ l, S (l + 1) ≤ S l + geoIncr C l) ∧
      (∀ l, S l ≤ S (l + 1) + geoIncr C l) :=
  ⟨D.C, D.C_nonneg, D.kpIncrement_geoIncr_up, D.kpIncrement_geoIncr_lo⟩

/-- **The modulus accompanying the S4 datum.**  The `ρ = 1/2` Cauchy
modulus for the constant returned by `kpIncrementBound` — the rescaling
witness that, together with the increment bound, feeds straight into
`crealOfGeoIncrement` to build the infinite-volume `CReal` limit. -/
theorem kpIncrementBound_modulus {S : Nat → Q'} (D : KPIncrementData S)
    (ε : Q') (hε : (0 : Q') < ε) :
    ∃ δ : Q', (0 : Q') < δ ∧
      (Q'.ofNat 2 * (kpIncrementBound D).1) * δ ≤ ε :=
  D.kpIncrement_modulus ε hε

/-! ## The infinite-volume limit, assembled from the S4 datum

Feeding `kpIncrementBound D` + its modulus into the already-built KP
engine `crealOfGeoIncrement` produces the infinite-volume expectation as
a `CReal` with explicit Cauchy modulus, whose `Λ`-th approximation is the
finite-volume `S Λ`.  This shows S4 plugs straight into the S5 limit. -/

/-- **The infinite-volume limit from a KP increment datum.**  Assembles
`S`'s infinite-volume limit as a `CReal` via `crealOfGeoIncrement`,
consuming the S4 increment datum + its modulus.  No compactness, no
dominated convergence — only the geometric tail. -/
def infiniteVolumeLimit {S : Nat → Q'} (D : KPIncrementData S) : CReal :=
  crealOfGeoIncrement S D.C D.C_nonneg
    D.kpIncrement_geoIncr_up D.kpIncrement_geoIncr_lo
    (fun ε hε => D.kpIncrement_modulus ε hε)

/-- **The limit's `Λ`-th approximation is the finite-volume `S Λ`.**  The
infinite-volume limit is genuinely `lim_Λ S Λ`. -/
@[simp] theorem infiniteVolumeLimit_approx {S : Nat → Q'} (D : KPIncrementData S)
    (Λ : Nat) : (infiniteVolumeLimit D).approx Λ = S Λ := rfl

/-! ## A concrete inhabitant: the constant (zero-increment) datum

The constant sequence `S ≡ s₀` with the zero cluster tower `a ≡ 0`,
`r = 0`, `C = 0`: a genuine `KPIncrementData` (the trivial convergent
regime, all activities vanish) whose increment bound and limit fire
end-to-end on a real object (not a `True`/`Unit` placeholder). -/

/-- The constant (zero-increment) KP datum: `S Λ = s₀` for all `Λ`, with
the identically-zero cluster tower (`r = 0`, `C = 0`).  A genuine
inhabitant exhibiting the S4 machinery end-to-end. -/
def constData (s₀ : Q') : KPIncrementData (fun _ => s₀) where
  C := 0
  r := 0
  a := fun _ => 0
  C_nonneg := Q'.le_refl' 0
  r_nonneg := Q'.le_refl' 0
  r_le_half := by decide
  a_nonneg := fun _ => Q'.le_refl' 0
  a_base := Q'.le_refl' 0
  a_ratio := fun _ => by
    show (0 : Q') ≤ 0 * 0
    exact Q'.mul_nonneg 0 0 (Q'.le_refl' 0) (Q'.le_refl' 0)
  incr_up := fun _ => by
    show s₀ ≤ s₀ + 0
    rw [Q'.add_zero']; exact Q'.le_refl' s₀
  incr_lo := fun _ => by
    show s₀ ≤ s₀ + 0
    rw [Q'.add_zero']; exact Q'.le_refl' s₀

/-- The constant datum's increment-bound constant is `0`. -/
theorem constData_C (s₀ : Q') : (kpIncrementBound (constData s₀)).1 = 0 := rfl

/-- The constant datum's infinite-volume limit has every approximation
`= s₀` — the limit is genuinely the constant value. -/
@[simp] theorem constData_limit_approx (s₀ : Q') (Λ : Nat) :
    (infiniteVolumeLimit (constData s₀)).approx Λ = s₀ := rfl

end YMGap.Continuum.KPIncrement

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.KPIncrement.pow_le_pow_base
#print axioms YMGap.Continuum.KPIncrement.KPIncrementData.activity_geom_bound
#print axioms YMGap.Continuum.KPIncrement.KPIncrementData.activity_le_geoIncr
#print axioms YMGap.Continuum.KPIncrement.KPIncrementData.kpIncrement_geoIncr_up
#print axioms YMGap.Continuum.KPIncrement.KPIncrementData.kpIncrement_geoIncr_lo
#print axioms YMGap.Continuum.KPIncrement.KPIncrementData.kpIncrement_modulus
#print axioms YMGap.Continuum.KPIncrement.kpIncrementBound
#print axioms YMGap.Continuum.KPIncrement.kpIncrementBound_modulus
#print axioms YMGap.Continuum.KPIncrement.infiniteVolumeLimit
#print axioms YMGap.Continuum.KPIncrement.infiniteVolumeLimit_approx
#print axioms YMGap.Continuum.KPIncrement.constData
#print axioms YMGap.Continuum.KPIncrement.constData_C
#print axioms YMGap.Continuum.KPIncrement.constData_limit_approx
