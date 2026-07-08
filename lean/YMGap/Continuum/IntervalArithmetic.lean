/-
Item 12 (Koch–Wittwer certified-RG route) — **THE SOUND Q' INTERVAL-ARITHMETIC
KERNEL.**

# What this module is (read first)

This is the certified-arithmetic engine for the rigorous computer-assisted
renormalization-group route to `singleStep`
(`docs/alternative-routes-to-singlestep.md` item 12; scouting
`docs/balaban-scouting.md`).  Koch–Wittwer-style proofs certify contraction of an
RG map by RIGOROUS INTERVAL ARITHMETIC — every real quantity is enclosed in an
interval whose endpoints are exact and whose enclosure is machine-proved to be
preserved under the arithmetic.  Because this project's `Q'` substrate is EXACT
rationals with `decide`-checkable order (`YMGap/Constructive/Rationals.lean`),
outward rounding is automatic and the interval endpoints are exact — the part
Koch–Wittwer had to build by hand is free here.

An enclosure is a `QI` (a pair `lo ≤ hi` of `Q'` endpoints).  The LOAD-BEARING
content of this file is the SOUNDNESS of the interval operations: for each op we
prove that if the inputs enclose real values, the output encloses the
corresponding real value (`contains_add`, `contains_neg`, `contains_sub`,
`contains_mul` — the 4-corner rule, the classic interval-multiplication soundness
— and `contains_scale`).  These are genuine theorems, not assumptions: the
enclosure is preserved.

`certifiedLt` turns a `decide`-checkable endpoint fact (`i.hi < c`) into a bound on
EVERY enclosed value — the mechanism by which a `decide` on rational endpoints
certifies an analytic inequality.

# Scope / honesty (AGENTS.md Rule 6 / Rule 9)

This is the KERNEL only.  It inhabits NO frontier type.  The certified contraction
on the truncated block-spin map and the named truncation-error residual live in
`YMGap/Continuum/TruncatedBlockSpinContraction.lean`.  Nothing here closes any part
of the Clay problem.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Int`/`Nat` composition.  Every load-bearing soundness theorem is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  The endpoints `lo hi : Q'` are
`Type`-level data (Rule 8); the enclosure witness `le : lo ≤ hi` and the
`contains` predicate are genuine propositional side conditions carrying no erased
modulus.
-/

import YMGap.Constructive.AbsQ
import YMGap.Constructive.QPoly

namespace YMGap.Continuum.IntervalArithmetic

open YMGap.Constructive
open YMGap.Constructive.Q'

/-! ## 0. Small `Q'` order facts used by the kernel (proved here, axiom-clean) -/

/-- Constructive totality of `Q'.le`, straight from `Int.le_total` on the
cross-product representation (no Classical: `Int` order is decidable/total in
Lean core). -/
theorem le_total (a b : Q') : a ≤ b ∨ b ≤ a := by
  rcases Int.le_total (a.num * (b.den : Int)) (b.num * (a.den : Int)) with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Middle-factor swap on `Int` (private helper for strict transitivity). -/
private theorem imrc (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_comm b c, ← Int.mul_assoc]

/-- `a ≤ b`, `b < c` ⟹ `a < c` on `Q'` (the strict-on-the-right transitivity the
`certifiedLt` mechanism needs).  Cross-product argument, cancelling the middle
denominator via `Int.lt_of_mul_lt_mul_right`. -/
theorem q_lt_of_le_of_lt {p q r : Q'} (h_pq : p ≤ q) (h_qr : q < r) : p < r := by
  show p.num * (r.den : Int) < r.num * (p.den : Int)
  have h1 : p.num * (q.den : Int) ≤ q.num * (p.den : Int) := h_pq
  have h2 : q.num * (r.den : Int) < r.num * (q.den : Int) := h_qr
  have hr : (0 : Int) ≤ (r.den : Int) := Int.natCast_nonneg _
  have hppos : (0 : Int) < (p.den : Int) := by exact_mod_cast Q'.den_pos p
  have step1 : p.num * (q.den : Int) * (r.den : Int)
             ≤ q.num * (p.den : Int) * (r.den : Int) :=
    Int.mul_le_mul_of_nonneg_right h1 hr
  have step2 : q.num * (r.den : Int) * (p.den : Int)
             < r.num * (q.den : Int) * (p.den : Int) :=
    Int.mul_lt_mul_of_pos_right h2 hppos
  have e1 : q.num * (p.den : Int) * (r.den : Int)
          = q.num * (r.den : Int) * (p.den : Int) := imrc _ _ _
  have e2 : r.num * (q.den : Int) * (p.den : Int)
          = r.num * (p.den : Int) * (q.den : Int) := imrc _ _ _
  have e3 : p.num * (q.den : Int) * (r.den : Int)
          = p.num * (r.den : Int) * (q.den : Int) := imrc _ _ _
  have chain : p.num * (r.den : Int) * (q.den : Int)
             < r.num * (p.den : Int) * (q.den : Int) := by
    calc p.num * (r.den : Int) * (q.den : Int)
        = p.num * (q.den : Int) * (r.den : Int) := e3.symm
      _ ≤ q.num * (p.den : Int) * (r.den : Int) := step1
      _ = q.num * (r.den : Int) * (p.den : Int) := e1
      _ < r.num * (q.den : Int) * (p.den : Int) := step2
      _ = r.num * (p.den : Int) * (q.den : Int) := e2
  exact Int.lt_of_mul_lt_mul_right chain (Int.natCast_nonneg _)

/-! ### `min'` / `max'` order facts (from the decidable `≤` split + `le_total`) -/

theorem min'_le_left (p q : Q') : Q'.min' p q ≤ p := by
  unfold Q'.min'
  split
  · exact Q'.le_refl' p
  · rename_i h
    rcases le_total p q with hpq | hqp
    · exact absurd hpq h
    · exact hqp

theorem min'_le_right (p q : Q') : Q'.min' p q ≤ q := by
  unfold Q'.min'
  split
  · rename_i h; exact h
  · exact Q'.le_refl' q

theorem le_min' {r p q : Q'} (hp : r ≤ p) (hq : r ≤ q) : r ≤ Q'.min' p q := by
  unfold Q'.min'
  split
  · exact hp
  · exact hq

theorem le_max'_left (p q : Q') : p ≤ Q'.max' p q := by
  unfold Q'.max'
  split
  · rename_i h; exact h
  · exact Q'.le_refl' p

theorem le_max'_right (p q : Q') : q ≤ Q'.max' p q := by
  unfold Q'.max'
  split
  · exact Q'.le_refl' q
  · rename_i h
    rcases le_total p q with hpq | hqp
    · exact absurd hpq h
    · exact hqp

theorem max'_le {p q r : Q'} (hp : p ≤ r) (hq : q ≤ r) : Q'.max' p q ≤ r := by
  unfold Q'.max'
  split
  · exact hq
  · exact hp

/-! ### Multiplication by a nonpositive factor (order reversal) -/

/-- `a ≤ b`, `c ≤ 0` ⟹ `b·c ≤ a·c`.  Derived from the nonneg version applied to
`-c ≥ 0` and `Q'.neg_le_neg`. -/
theorem mul_le_mul_of_nonpos_right (a b c : Q') (hab : a ≤ b) (hc : c ≤ (0 : Q')) :
    b * c ≤ a * c := by
  have hnc : (0 : Q') ≤ -c := Q'.neg_le_neg hc
  have h1 : a * (-c) ≤ b * (-c) := Q'.mul_le_mul_of_nonneg_right a b (-c) hab hnc
  -- -(a*c) ≤ -(b*c)
  have h2 : (-(a * c)) ≤ (-(b * c)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_neg_eqv a c))
      (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_neg_eqv b c)))
  -- b*c ≤ a*c
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv (b * c)))
    (Q'.le_trans' _ _ _ (Q'.neg_le_neg h2) (Q'.le_of_eqv (Q'.neg_neg_eqv (a * c))))

/-- `a ≤ b`, `c ≤ 0` ⟹ `c·b ≤ c·a`.  Left version, via commutativity. -/
theorem mul_le_mul_of_nonpos_left (a b c : Q') (hab : a ≤ b) (hc : c ≤ (0 : Q')) :
    c * b ≤ c * a := by
  have h := mul_le_mul_of_nonpos_right a b c hab hc  -- b*c ≤ a*c
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c b))
    (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (Q'.mul_comm_eqv c a)))

/-! ### One-factor monotone-enclosure lemmas (the core of interval mul)

For `a ≤ x ≤ b` and any (sign-unknown) constant `c`, the product with `c` is
enclosed in the interval spanned by the two endpoint products — regardless of the
sign of `c`.  This is the standard "linear in each variable ⟹ extremal at
endpoints" fact, proved by a constructive split on `0 ≤ c` / `c ≤ 0`. -/

/-- Constant on the RIGHT: `x·c ∈ [min(a·c, b·c), max(a·c, b·c)]`. -/
theorem mul_mem_right (a b x c : Q') (h1 : a ≤ x) (h2 : x ≤ b) :
    Q'.min' (a * c) (b * c) ≤ x * c ∧ x * c ≤ Q'.max' (a * c) (b * c) := by
  rcases le_total 0 c with hc | hc
  · have lo : a * c ≤ x * c := Q'.mul_le_mul_of_nonneg_right a x c h1 hc
    have hi : x * c ≤ b * c := Q'.mul_le_mul_of_nonneg_right x b c h2 hc
    exact ⟨Q'.le_trans' _ _ _ (min'_le_left (a * c) (b * c)) lo,
           Q'.le_trans' _ _ _ hi (le_max'_right (a * c) (b * c))⟩
  · have lo : x * c ≤ a * c := mul_le_mul_of_nonpos_right a x c h1 hc
    have hi : b * c ≤ x * c := mul_le_mul_of_nonpos_right x b c h2 hc
    exact ⟨Q'.le_trans' _ _ _ (min'_le_right (a * c) (b * c)) hi,
           Q'.le_trans' _ _ _ lo (le_max'_left (a * c) (b * c))⟩

/-- Constant on the LEFT: `c·x ∈ [min(c·a, c·b), max(c·a, c·b)]`. -/
theorem mul_mem_left (c a b x : Q') (h1 : a ≤ x) (h2 : x ≤ b) :
    Q'.min' (c * a) (c * b) ≤ c * x ∧ c * x ≤ Q'.max' (c * a) (c * b) := by
  rcases le_total 0 c with hc | hc
  · have lo : c * a ≤ c * x := Q'.mul_le_mul_of_nonneg_left a x c h1 hc
    have hi : c * x ≤ c * b := Q'.mul_le_mul_of_nonneg_left x b c h2 hc
    exact ⟨Q'.le_trans' _ _ _ (min'_le_left (c * a) (c * b)) lo,
           Q'.le_trans' _ _ _ hi (le_max'_right (c * a) (c * b))⟩
  · have lo : c * x ≤ c * a := mul_le_mul_of_nonpos_left a x c h1 hc
    have hi : c * b ≤ c * x := mul_le_mul_of_nonpos_left x b c h2 hc
    exact ⟨Q'.le_trans' _ _ _ (min'_le_right (c * a) (c * b)) hi,
           Q'.le_trans' _ _ _ lo (le_max'_left (c * a) (c * b))⟩

/-! ## 1. The enclosure type `QI` and the containment predicate -/

/-- An **enclosure**: a rational interval `[lo, hi]` (with `lo ≤ hi`) certifying a
real quantity to lie between exact rational endpoints.  `lo`/`hi` are `Type`-level
`Q'` data; `le` is the propositional validity of the enclosure. -/
structure QI where
  lo : Q'
  hi : Q'
  le : lo ≤ hi

/-- `contains i x` : the value `x` lies in the enclosure `i`. -/
def contains (i : QI) (x : Q') : Prop := i.lo ≤ x ∧ x ≤ i.hi

/-- The width `hi − lo` of an enclosure (a measure of certified precision). -/
def width (i : QI) : Q' := i.hi - i.lo

/-- The point (degenerate) enclosure `[c, c]`. -/
def point (c : Q') : QI := ⟨c, c, Q'.le_refl' c⟩

theorem contains_point (c : Q') : contains (point c) c :=
  ⟨Q'.le_refl' c, Q'.le_refl' c⟩

/-! ## 2. Certified operations + SOUNDNESS (enclosure preservation) -/

/-- Interval addition `[a,b] + [c,d] = [a+c, b+d]`. -/
def add (i j : QI) : QI :=
  ⟨i.lo + j.lo, i.hi + j.hi,
    Q'.le_trans' _ _ _ (Q'.add_le_add_right i.lo i.hi j.lo i.le)
      (Q'.add_le_add_left i.hi j.lo j.hi j.le)⟩

/-- **SOUNDNESS of `add`** — the sum of enclosed values is enclosed by the sum. -/
theorem contains_add {i j : QI} {x y : Q'}
    (hx : contains i x) (hy : contains j y) : contains (add i j) (x + y) := by
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.add_le_add_right i.lo x j.lo hx.1)
      (Q'.add_le_add_left x j.lo y hy.1)
  · exact Q'.le_trans' _ _ _ (Q'.add_le_add_right x i.hi y hx.2)
      (Q'.add_le_add_left i.hi y j.hi hy.2)

/-- Interval negation `-[a,b] = [-b, -a]`. -/
def neg (i : QI) : QI := ⟨-i.hi, -i.lo, Q'.neg_le_neg i.le⟩

/-- **SOUNDNESS of `neg`.** -/
theorem contains_neg {i : QI} {x : Q'} (hx : contains i x) :
    contains (neg i) (-x) :=
  ⟨Q'.neg_le_neg hx.2, Q'.neg_le_neg hx.1⟩

/-- Interval subtraction `i − j := i + (−j)`. -/
def sub (i j : QI) : QI := add i (neg j)

/-- **SOUNDNESS of `sub`** (`x − y = x + (−y)` definitionally on `Q'`). -/
theorem contains_sub {i j : QI} {x y : Q'}
    (hx : contains i x) (hy : contains j y) : contains (sub i j) (x - y) := by
  show contains (add i (neg j)) (x + (-y))
  exact contains_add hx (contains_neg hy)

/-! ### Interval multiplication — the 4-corner rule -/

/-- Max of the four corner products. -/
def prod4max (ll lh hl hh : Q') : Q' := Q'.max' (Q'.max' ll lh) (Q'.max' hl hh)

/-- Min of the four corner products. -/
def prod4min (ll lh hl hh : Q') : Q' := Q'.min' (Q'.min' ll lh) (Q'.min' hl hh)

theorem ll_le_prod4max (ll lh hl hh : Q') : ll ≤ prod4max ll lh hl hh :=
  Q'.le_trans' _ _ _ (le_max'_left ll lh) (le_max'_left (Q'.max' ll lh) (Q'.max' hl hh))
theorem lh_le_prod4max (ll lh hl hh : Q') : lh ≤ prod4max ll lh hl hh :=
  Q'.le_trans' _ _ _ (le_max'_right ll lh) (le_max'_left (Q'.max' ll lh) (Q'.max' hl hh))
theorem hl_le_prod4max (ll lh hl hh : Q') : hl ≤ prod4max ll lh hl hh :=
  Q'.le_trans' _ _ _ (le_max'_left hl hh) (le_max'_right (Q'.max' ll lh) (Q'.max' hl hh))
theorem hh_le_prod4max (ll lh hl hh : Q') : hh ≤ prod4max ll lh hl hh :=
  Q'.le_trans' _ _ _ (le_max'_right hl hh) (le_max'_right (Q'.max' ll lh) (Q'.max' hl hh))

theorem prod4min_le_ll (ll lh hl hh : Q') : prod4min ll lh hl hh ≤ ll :=
  Q'.le_trans' _ _ _ (min'_le_left (Q'.min' ll lh) (Q'.min' hl hh)) (min'_le_left ll lh)
theorem prod4min_le_lh (ll lh hl hh : Q') : prod4min ll lh hl hh ≤ lh :=
  Q'.le_trans' _ _ _ (min'_le_left (Q'.min' ll lh) (Q'.min' hl hh)) (min'_le_right ll lh)
theorem prod4min_le_hl (ll lh hl hh : Q') : prod4min ll lh hl hh ≤ hl :=
  Q'.le_trans' _ _ _ (min'_le_right (Q'.min' ll lh) (Q'.min' hl hh)) (min'_le_left hl hh)
theorem prod4min_le_hh (ll lh hl hh : Q') : prod4min ll lh hl hh ≤ hh :=
  Q'.le_trans' _ _ _ (min'_le_right (Q'.min' ll lh) (Q'.min' hl hh)) (min'_le_right hl hh)

theorem prod4min_le_prod4max (ll lh hl hh : Q') :
    prod4min ll lh hl hh ≤ prod4max ll lh hl hh :=
  Q'.le_trans' _ _ _ (prod4min_le_ll ll lh hl hh) (ll_le_prod4max ll lh hl hh)

/-- Interval multiplication `[a,b]·[c,d]` = the 4-corner enclosure. -/
def mul (i j : QI) : QI :=
  ⟨prod4min (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi),
   prod4max (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi),
   prod4min_le_prod4max _ _ _ _⟩

/-- **SOUNDNESS of `mul`** — the 4-corner rule encloses the product.  The classic
interval-multiplication soundness: fix `x`, bound `x·y` between `x·j.lo` and
`x·j.hi` (`mul_mem_left`); then bound each of those between corner products
(`mul_mem_right`); assemble through `min'`/`max'`. -/
theorem contains_mul {i j : QI} {x y : Q'}
    (hx : contains i x) (hy : contains j y) : contains (mul i j) (x * y) := by
  obtain ⟨hxl, hxh⟩ := hx
  obtain ⟨hyl, hyh⟩ := hy
  -- Step 1: x*y ∈ [min(x*jlo, x*jhi), max(x*jlo, x*jhi)]  (const = x on the left)
  obtain ⟨s1lo, s1hi⟩ := mul_mem_left x j.lo j.hi y hyl hyh
  -- Step 2a: x*jlo ∈ [min(ll, hl), max(ll, hl)]  (const = j.lo on the right)
  obtain ⟨s2alo, s2ahi⟩ := mul_mem_right i.lo i.hi x j.lo hxl hxh
  -- Step 2b: x*jhi ∈ [min(lh, hh), max(lh, hh)]  (const = j.hi on the right)
  obtain ⟨s2blo, s2bhi⟩ := mul_mem_right i.lo i.hi x j.hi hxl hxh
  show prod4min (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi) ≤ x * y
     ∧ x * y ≤ prod4max (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi)
  refine ⟨?_, ?_⟩
  · -- prod4min ≤ x*y  (via prod4min ≤ min(x*jlo,x*jhi) ≤ x*y)
    have hxjlo : prod4min (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi)
        ≤ x * j.lo :=
      Q'.le_trans' _ _ _
        (le_min' (prod4min_le_ll _ _ _ _) (prod4min_le_hl _ _ _ _)) s2alo
    have hxjhi : prod4min (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi)
        ≤ x * j.hi :=
      Q'.le_trans' _ _ _
        (le_min' (prod4min_le_lh _ _ _ _) (prod4min_le_hh _ _ _ _)) s2blo
    exact Q'.le_trans' _ _ _ (le_min' hxjlo hxjhi) s1lo
  · -- x*y ≤ prod4max
    have hxjlo : x * j.lo
        ≤ prod4max (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi) :=
      Q'.le_trans' _ _ _ s2ahi
        (max'_le (ll_le_prod4max _ _ _ _) (hl_le_prod4max _ _ _ _))
    have hxjhi : x * j.hi
        ≤ prod4max (i.lo * j.lo) (i.lo * j.hi) (i.hi * j.lo) (i.hi * j.hi) :=
      Q'.le_trans' _ _ _ s2bhi
        (max'_le (lh_le_prod4max _ _ _ _) (hh_le_prod4max _ _ _ _))
    exact Q'.le_trans' _ _ _ s1hi (max'_le hxjlo hxjhi)

/-- Scaling an enclosure by a (sign-unknown) constant `c`, via `mul` with the
point interval `[c,c]`. -/
def scale (c : Q') (i : QI) : QI := mul (point c) i

/-- **SOUNDNESS of `scale`.** -/
theorem contains_scale {i : QI} {c x : Q'} (hx : contains i x) :
    contains (scale c i) (c * x) :=
  contains_mul (contains_point c) hx

/-! ## 3. Certified endpoint comparison — a `decide`-checked bound on the
enclosed quantity -/

/-- **`certifiedLt`** — a `decide`-checkable upper endpoint fact `i.hi < c`
certifies `x < c` for EVERY enclosed `x`.  This is the mechanism by which a
`decide` on rational interval endpoints discharges an analytic strict inequality
about the (unknown, enclosed) real quantity. -/
theorem certifiedLt (i : QI) (c : Q') (h : i.hi < c) :
    ∀ x, contains i x → x < c :=
  fun _ hx => q_lt_of_le_of_lt hx.2 h

/-- **`certifiedLe`** — the non-strict companion: `i.hi ≤ c` certifies `x ≤ c` for
every enclosed `x`. -/
theorem certifiedLe (i : QI) (c : Q') (h : i.hi ≤ c) :
    ∀ x, contains i x → x ≤ c :=
  fun _ hx => Q'.le_trans' _ _ _ hx.2 h

/-- **`certifiedLowerLe`** — a lower endpoint fact `c ≤ i.lo` certifies `c ≤ x`
for every enclosed `x`. -/
theorem certifiedLowerLe (i : QI) (c : Q') (h : c ≤ i.lo) :
    ∀ x, contains i x → c ≤ x :=
  fun _ hx => Q'.le_trans' _ _ _ h hx.1

end YMGap.Continuum.IntervalArithmetic

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.IntervalArithmetic.le_total
#print axioms YMGap.Continuum.IntervalArithmetic.q_lt_of_le_of_lt
#print axioms YMGap.Continuum.IntervalArithmetic.mul_le_mul_of_nonpos_right
#print axioms YMGap.Continuum.IntervalArithmetic.mul_mem_right
#print axioms YMGap.Continuum.IntervalArithmetic.mul_mem_left
#print axioms YMGap.Continuum.IntervalArithmetic.contains_add
#print axioms YMGap.Continuum.IntervalArithmetic.contains_neg
#print axioms YMGap.Continuum.IntervalArithmetic.contains_sub
#print axioms YMGap.Continuum.IntervalArithmetic.contains_mul
#print axioms YMGap.Continuum.IntervalArithmetic.contains_scale
#print axioms YMGap.Continuum.IntervalArithmetic.certifiedLt
#print axioms YMGap.Continuum.IntervalArithmetic.certifiedLe
