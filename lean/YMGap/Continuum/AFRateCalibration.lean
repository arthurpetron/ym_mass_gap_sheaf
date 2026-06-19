/-
Track B / R2 — the ASYMPTOTIC-FREEDOM RATE modulus as a named interface, and the
HARMONIC-DIVERGENCE diagnostic that proves the LINEAR bond-moving crack cannot
close the continuum mountain.

# Why this module exists — the linear crack is provably insufficient

The upstream bond-moving step proves the FAVORABLE per-step modulus
`δ(w_k, p) ≤ 6p·(1 − w_k)` (the deviation of the bond-moved data from pure
heat-kernel form vanishes linearly in the weak-coupling margin `1 − w_k`).  The
open 4D content is the ACCUMULATION `∑_k δ(w_k, p) < ∞` along the
asymptotic-freedom (AF) trajectory `w_k → 1`.

The standard two-loop AF running predicts the rate of approach: the per-scale
margin behaves like the running coupling squared, `1 − w_k ≍ g_k² ≍ 1/k`.  This
module makes that rate a NAMED interface (`AFRateModulus`) and then proves the
DECISIVE NEGATIVE DIAGNOSTIC: the partial sums of `1/(k+B)` exceed every bound
(`harmonic_diverges`).  Consequently the LINEAR bound
`∑_k 6p·(1 − w_k) ≥ ∑_k 6p·A'/(k+B)` is bounded BELOW by a divergent harmonic
series — so the linear crack CANNOT be summable
(`linear_bound_not_summable`).

The verdict this module establishes: the per-step `δ → 0` linear modulus, while
genuine, is by itself too weak to close the bond-moving summability.  The
renormalized QUADRATIC defect `δ_ren ≤ C·(1 − w)²`, whose lower-bound side
`∑ 1/k²` converges, is what is needed.  This is a sharp diagnostic about WHICH
estimate can work — it does not itself supply the quadratic bound.

# What is GENUINELY PROVED here — and what is a NAMED interface (honest)

PROVED (pure `Q'`/`Nat` analysis, axiom-clean):

  * `harmonic_diverges` — for every bound `M : Q'` there is an EXPLICIT prefix
    length `N` with `M ≤ ∑_{k<N} 1/(k+B)`.  The witness `N(M)` is constructed by
    iterated DOUBLING: each block `[m, 2m)` with `m` large enough contributes at
    least `1/3` to the sum (it has `m` terms each `≥ 1/(2m+…)` and `m·1/(3m) =
    1/3`), so enough doublings overshoot any `M`.

  * `linear_bound_not_summable` — under a TWO-SIDED AF rate
    (`A'/(k+B) ≤ 1 − w_k`), the linear bond-moving budget
    `∑_{k<N} 6p·(1 − w_k)` exceeds every bound `R`; hence NO finite summability
    constant exists for the linear crack.

NAMED INTERFACE (NOT derived — the standard two-loop AF input):

  * `AFRateModulus` — the obligation `1 − w_k ≤ A/(k+B)` (and, two-sided,
    `A'/(k+B) ≤ 1 − w_k`).  This encodes the two-loop AF trajectory rate
    `1 − w_k ≍ g_k² ≍ 1/k`; it is the AF physics input, packaged as a
    `Type`-level structure with all moduli as data, and given a trivial concrete
    inhabitant (`afRateModulus_canonical`) so the interface is non-vacuous.  It
    is NOT proved here.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic at the `Int` cross-product level, structural Nat
inductions, the positivity-guarded `Q'.divPos`, and reused `Q'` order lemmas.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.AFRateCalibration

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep

/-! ## −1. Small generic `Q'` order helpers (proved here, axiom-clean)

Three elementary order facts not present in the foundation: two-sided additive
monotonicity, right-cancellation of a positive factor, and the decidable
dichotomy `a ≤ b ∨ b < a`.  All reduce to `Int` cross-products. -/

/-- Two-sided additive monotonicity: `a ≤ b → c ≤ d → a + c ≤ b + d`. -/
theorem q_add_le_add {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c hab) (Q'.add_le_add_left b c d hcd)

/-- Right-cancellation of a positive factor: `a·c ≤ b·c → 0 < c → a ≤ b`. -/
theorem q_le_of_mul_le_mul_right (a b c : Q') (hc : (0 : Q') < c)
    (h : a * c ≤ b * c) : a ≤ b := by
  -- a*c ≤ b*c is (a.num·c.den)·(b.den·c.den) ≤ (b.num·c.den)·(a.den·c.den).
  -- We want a.num·b.den ≤ b.num·a.den.  Strip the common positive c.den·c.den.
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int)
  have hcnum : (0 : Int) < c.num := Q'.num_pos_of_pos hc
  have hcden : (0 : Int) < (c.den : Int) := by exact_mod_cast c.den_pos
  have hkey : (0 : Int) < c.num * (c.den : Int) := Int.mul_pos hcnum hcden
  -- h at cross-product level:
  have h' : (a * c).num * ((b * c).den : Int) ≤ (b * c).num * ((a * c).den : Int) := h
  -- (a*c).num = a.num·c.num ; (a*c).den = a.den·c.den.
  have ean : (a * c).num = a.num * c.num := rfl
  have ead : ((a * c).den : Int) = (a.den : Int) * (c.den : Int) := by
    show ((a.den * c.den : Nat) : Int) = (a.den : Int) * (c.den : Int); push_cast; rfl
  have ebn : (b * c).num = b.num * c.num := rfl
  have ebd : ((b * c).den : Int) = (b.den : Int) * (c.den : Int) := by
    show ((b.den * c.den : Nat) : Int) = (b.den : Int) * (c.den : Int); push_cast; rfl
  rw [ean, ead, ebn, ebd] at h'
  -- h' : (a.num·c.num)·(b.den·c.den) ≤ (b.num·c.num)·(a.den·c.den).
  -- rearrange to (a.num·b.den)·(c.num·c.den) ≤ (b.num·a.den)·(c.num·c.den).
  have hL : (a.num * c.num) * ((b.den : Int) * (c.den : Int))
      = (a.num * (b.den : Int)) * (c.num * (c.den : Int)) := by ac_rfl
  have hR : (b.num * c.num) * ((a.den : Int) * (c.den : Int))
      = (b.num * (a.den : Int)) * (c.num * (c.den : Int)) := by ac_rfl
  rw [hL, hR] at h'
  exact Int.le_of_mul_le_mul_right h' hkey

/-- Decidable dichotomy on `Q'`: `a ≤ b` or `b < a`. -/
theorem q_le_or_lt (a b : Q') : a ≤ b ∨ b < a := by
  -- a ≤ b is a.num·b.den ≤ b.num·a.den ; b < a is b.num·a.den < a.num·b.den.
  rcases Int.lt_or_le (b.num * (a.den : Int)) (a.num * (b.den : Int)) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-! ## 0. The harmonic term `1/(k+B)` and its partial sums (in `Q'`) -/

/-- The denominator `k + B` of the harmonic term, with `k : Nat` embedded. -/
def harmDen (B : Q') (k : Nat) : Q' := Q'.ofNat k + B

/-- `k + B > 0` for `B > 0` (`ofNat k ≥ 0`, `B > 0`). -/
theorem harmDen_pos {B : Q'} (hB : (0 : Q') < B) (k : Nat) :
    (0 : Q') < harmDen B k := by
  -- ofNat k + B : flip to B + ofNat k via pos_add_nonneg, then commute
  show (0 : Q') < Q'.ofNat k + B
  have h : (0 : Q') < B + Q'.ofNat k :=
    Q'.pos_add_nonneg hB (zero_le_ofNat k)
  exact lt_of_lt_of_le h (Q'.le_of_eqv (Q'.add_comm_eqv B (Q'.ofNat k)))

/-- The harmonic term `1/(k+B)`, as the positivity-guarded quotient. -/
def harmTerm (B : Q') (hB : (0 : Q') < B) (k : Nat) : Q' :=
  Q'.divPos 1 (harmDen B k) (harmDen_pos hB k)

theorem harmTerm_pos {B : Q'} (hB : (0 : Q') < B) (k : Nat) :
    (0 : Q') < harmTerm B hB k :=
  Q'.divPos_pos 1 (harmDen B k) (harmDen_pos hB k) (by decide)

theorem harmTerm_nonneg {B : Q'} (hB : (0 : Q') < B) (k : Nat) :
    (0 : Q') ≤ harmTerm B hB k :=
  Q'.le_of_lt (harmTerm_pos hB k)

/-- The harmonic partial sum `∑_{k<N} 1/(k+B)` (reusing `BondMovingStep.fsum`). -/
def harmSum (B : Q') (hB : (0 : Q') < B) (N : Nat) : Q' :=
  fsum (harmTerm B hB) N

theorem harmSum_nonneg {B : Q'} (hB : (0 : Q') < B) (N : Nat) :
    (0 : Q') ≤ harmSum B hB N :=
  fsum_nonneg (harmTerm_nonneg hB) N

/-! ## 1. `fsum` monotonicity / range facts (pure `Q'`)

The divergence proof needs three elementary `fsum` facts: monotonicity in the
upper limit, a termwise lower bound, and the "sum of `n` copies of a constant
lower bound" estimate over a shifted block. -/

/-- `fsum` is monotone in its length for a nonnegative sequence:
`fsum f m ≤ fsum f n` when `m ≤ n`. -/
theorem fsum_le_of_le {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ {m n : Nat}, m ≤ n → fsum f m ≤ fsum f n := by
  intro m n hmn
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hmn
    subst this; exact Q'.le_refl' _
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
      have h1 : fsum f m ≤ fsum f k := ih hmk
      have h2 : fsum f k ≤ fsum f k + f k :=
        Q'.add_le_self_of_nonneg (fsum f k) (f k) (hf k)
      exact Q'.le_trans' _ _ _ h1 h2
    · have : m = k + 1 := Nat.le_antisymm hmn hge
      subst this; exact Q'.le_refl' _

/-- **The shifted-block lower bound.**  For a sequence `f` that is antitone in
the sense `i ≤ j → f j ≤ f i`, the sum of `n` consecutive terms starting at `a`
is at least `n` copies of the smallest one, `f (a + n)`:

    (ofNat n) · f (a + n)  ≤  ∑_{i<n} f (a + i).

Each of the `n` terms `f (a + i)` (with `i < n`, so `a + i ≤ a + n`) is
`≥ f (a + n)` by antitonicity; summing `n` of them gives `n · f(a+n)`. -/
theorem block_lower_bound {f : Nat → Q'}
    (hanti : ∀ {i j : Nat}, i ≤ j → f j ≤ f i) (a : Nat) :
    ∀ n, Q'.ofNat n * f (a + n) ≤ fsum (fun i => f (a + i)) n := by
  intro n
  induction n with
  | zero =>
    -- ofNat 0 * f a ≤ 0 ; LHS ≃ 0
    show Q'.ofNat 0 * f (a + 0) ≤ (0 : Q')
    have hz : (Q'.ofNat 0 * f (a + 0)).eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (f (a + 0)) ofNat_zero_eqv)
        (Q'.zero_mul_eqv (f (a + 0)))
    exact Q'.le_of_eqv hz
  | succ k ih =>
    -- ofNat (k+1) * f (a+k+1) ≤ fsum (..) k + f (a+k)
    -- Strategy: ofNat (k+1) * f(a+k+1) ≃ ofNat k * f(a+k+1) + f(a+k+1)
    --   ≤ ofNat k * f(a+k) + f(a+k) ≤ fsum (..) k + f(a+k).
    show Q'.ofNat (k + 1) * f (a + (k + 1))
        ≤ fsum (fun i => f (a + i)) k + f (a + k)
    -- split ofNat (k+1) = ofNat k + 1
    have hsplit : (Q'.ofNat (k + 1) * f (a + (k + 1))).eqv
        (Q'.ofNat k * f (a + (k + 1)) + f (a + (k + 1))) := by
      -- ofNat (k+1) ≃ ofNat k + 1, distribute
      have he : (Q'.ofNat (k + 1)).eqv (Q'.ofNat k + 1) := by
        refine Q'.eqv_trans _ _ _ (ofNat_add_eqv k 1) ?_
        exact Q'.add_eqv_congr_left (Q'.ofNat k) (Q'.ofNat 1) 1
          (Q'.eqv_of_eq rfl)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (f (a + (k + 1))) he) ?_
      refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv (Q'.ofNat k) 1 (f (a + (k + 1)))) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (f (a + (k + 1))))
    -- antitone: f (a + (k+1)) ≤ f (a + k)  (since a+k ≤ a+k+1)
    have hak : a + k ≤ a + (k + 1) := Nat.le_succ _
    have hanti_step : f (a + (k + 1)) ≤ f (a + k) := hanti hak
    -- ofNat k * f(a+k+1) ≤ ofNat k * f(a+k)  (mult by nonneg ofNat k on left)
    have hmul : Q'.ofNat k * f (a + (k + 1)) ≤ Q'.ofNat k * f (a + k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hanti_step (zero_le_ofNat k)
    -- ih : ofNat k * f (a + k) ≤ fsum (..) k
    -- assemble : ofNat k * f(a+k+1) + f(a+k+1) ≤ fsum(..) k + f(a+k)
    have hL : Q'.ofNat k * f (a + (k + 1)) + f (a + (k + 1))
        ≤ Q'.ofNat k * f (a + k) + f (a + k) :=
      q_add_le_add hmul hanti_step
    have hR : Q'.ofNat k * f (a + k) + f (a + k)
        ≤ fsum (fun i => f (a + i)) k + f (a + k) :=
      Q'.add_le_add_right _ _ (f (a + k)) ih
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) (Q'.le_trans' _ _ _ hL hR)

/-! ## 2. The harmonic term is antitone

`1/(k+B)` is antitone in `k`: for `i ≤ j`, `harmDen B i ≤ harmDen B j`, so the
reciprocals satisfy `1/(j+B) ≤ 1/(i+B)`.  Proved at the `divPos` level using the
`divPos_le_of_le_mul` / `le_divPos_of_mul_le` characterizations. -/

/-- `harmDen` is monotone in `k`: `i ≤ j → harmDen B i ≤ harmDen B j`. -/
theorem harmDen_mono (B : Q') {i j : Nat} (h : i ≤ j) :
    harmDen B i ≤ harmDen B j := by
  show Q'.ofNat i + B ≤ Q'.ofNat j + B
  exact Q'.add_le_add_right _ _ B (CReal.ofNat_le_ofNat h)

/-- **The harmonic term is antitone.**  `i ≤ j → 1/(j+B) ≤ 1/(i+B)`.
From `harmDen B i ≤ harmDen B j` and the quotient bounds: `1/(j+B) ≤ 1/(i+B)`
iff `(1/(j+B))·(i+B) ≤ 1`, which holds since `(1/(j+B))·(i+B) ≤ (1/(j+B))·(j+B)
≃ 1`. -/
theorem harmTerm_anti {B : Q'} (hB : (0 : Q') < B) {i j : Nat} (h : i ≤ j) :
    harmTerm B hB j ≤ harmTerm B hB i := by
  unfold harmTerm
  -- Goal: divPos 1 (den j) hj ≤ divPos 1 (den i) hi.
  -- Use divPos_le_of_le_mul with C = divPos 1 (den i) hi:
  --   suffices  1 ≤ (divPos 1 (den i) hi) * (den j).
  refine Q'.divPos_le_of_le_mul 1 (harmDen B j) (harmDen_pos hB j) ?_
  -- 1 ≤ divPos 1 (den i) hi * (den j).
  -- We have divPos 1 (den i) hi * (den i) ≃ 1, and (den i) ≤ (den j), and
  -- divPos 1 (den i) hi ≥ 0, so divPos 1 (den i) hi * (den i) ≤ divPos … * (den j).
  have hid : (Q'.divPos 1 (harmDen B i) (harmDen_pos hB i) * harmDen B i).eqv 1 :=
    Q'.divPos_mul_eqv 1 (harmDen B i) (harmDen_pos hB i)
  have hdmono : harmDen B i ≤ harmDen B j := harmDen_mono B h
  have hq_nonneg : (0 : Q') ≤ Q'.divPos 1 (harmDen B i) (harmDen_pos hB i) :=
    Q'.le_of_lt (Q'.divPos_pos 1 (harmDen B i) (harmDen_pos hB i) (by decide))
  have hstep : Q'.divPos 1 (harmDen B i) (harmDen_pos hB i) * harmDen B i
      ≤ Q'.divPos 1 (harmDen B i) (harmDen_pos hB i) * harmDen B j :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdmono hq_nonneg
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hid) hstep

/-! ## 3. The doubling step — each large block contributes at least `1/3`

For a block of `m` consecutive harmonic terms starting at index `m`
(i.e. `∑_{k ∈ [m, 2m)} 1/(k+B)`), the block-lower-bound gives
`≥ m · 1/(2m+B)`.  When `m` is large enough that `B ≤ ofNat m` (so the
denominator `2m + B ≤ 3m`), this is `≥ m/(3m) = 1/3`.  We package this as: the
prefix sum at `2m` exceeds the prefix sum at `m` by at least `1/3`. -/

/-- One third, as an explicit `Q'`. -/
def third : Q' := Q'.divPos 1 (Q'.ofNat 3) (by decide)

theorem third_pos : (0 : Q') < third :=
  Q'.divPos_pos 1 (Q'.ofNat 3) (by decide) (by decide)

/-- `fsum g (n+1) ≃ g 0 + ∑_{i<n} g (i+1)` — the "cons" reindex of a partial
sum: the first term peels off and the rest is the shifted sum. -/
theorem fsum_shift_cons (g : Nat → Q') :
    ∀ n, (fsum g (n + 1)).eqv (g 0 + fsum (fun i => g (i + 1)) n)
  | 0 => by
    show (fsum g 1).eqv (g 0 + fsum (fun i => g (i + 1)) 0)
    show ((0 : Q') + g 0).eqv (g 0 + (0 : Q'))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (g 0))) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (g 0)))
  | n + 1 => by
    show (fsum g (n + 1) + g (n + 1)).eqv
        (g 0 + fsum (fun i => g (i + 1)) (n + 1))
    have ih := fsum_shift_cons g n
    show (fsum g (n + 1) + g (n + 1)).eqv
        (g 0 + (fsum (fun i => g (i + 1)) n + g (n + 1)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (g (n + 1)) ih) ?_
    exact Q'.add_assoc_eqv (g 0) (fsum (fun i => g (i + 1)) n) (g (n + 1))

/-- The block-reindex bridge: appending term `k+k` to the `[k, …)`-shifted block
of length `k` equals prepending term `k` to the `[k+1, …)`-shifted block of
length `k`.  Both enumerate `harm` over the `k+1` consecutive indices `k … k+k`,
so the (commutative, associative) `Q'` sums agree. -/
theorem harm_block_reindex (B : Q') (hB : (0 : Q') < B) (k : Nat) :
    (fsum (fun i => harmTerm B hB (k + i)) k + harmTerm B hB (k + k)).eqv
      (harmTerm B hB k + fsum (fun i => harmTerm B hB ((k + 1) + i)) k) := by
  -- LHS is definitionally fsum (fun i => harm (k+i)) (k+1).
  have hLHS : fsum (fun i => harmTerm B hB (k + i)) k + harmTerm B hB (k + k)
      = fsum (fun i => harmTerm B hB (k + i)) (k + 1) := rfl
  rw [hLHS]
  -- reindex the inner block: harm ((k+1)+i) = harm (k+(i+1))
  have hreindex : (fun i => harmTerm B hB ((k + 1) + i))
      = (fun i => harmTerm B hB (k + (i + 1))) := by
    funext i
    have : (k + 1) + i = k + (i + 1) := by omega
    rw [this]
  rw [hreindex]
  -- fsum (fun i => harm (k+i)) (k+1) ≃ harm (k+0) + fsum (fun i => harm (k+(i+1))) k
  -- via fsum_shift_cons for g j := harm (k+j); g 0 = harm (k+0) = harm k.
  have hcons := fsum_shift_cons (fun j => harmTerm B hB (k + j)) k
  -- hcons : fsum g (k+1) ≃ g 0 + fsum (fun i => g (i+1)) k
  --   g 0 = harm (k+0); rewrite to harm k.
  have hg0 : harmTerm B hB (k + 0) = harmTerm B hB k := by
    have : k + 0 = k := Nat.add_zero k
    rw [this]
  -- assemble
  refine Q'.eqv_trans _ _ _ hcons ?_
  exact Q'.add_eqv_congr_right _ _ (fsum (fun i => harmTerm B hB (k + (i + 1))) k)
    (Q'.eqv_of_eq hg0)

/-- The successor step of `harm_split`, via the block-reindex bridge. -/
theorem harm_split_succ (B : Q') (hB : (0 : Q') < B) (k : Nat)
    (ih : (fsum (harmTerm B hB) (k + k)).eqv
      (fsum (harmTerm B hB) k
        + fsum (fun i => harmTerm B hB (k + i)) k)) :
    (fsum (harmTerm B hB) (k + k) + harmTerm B hB (k + k)
        + harmTerm B hB ((k + k) + 1)).eqv
      (fsum (harmTerm B hB) (k + 1)
        + fsum (fun i => harmTerm B hB ((k + 1) + i)) (k + 1)) := by
  -- Let A = fsum harm k, Sblk = fsum (shift k) k.
  -- RHS first: fsum harm (k+1) = A + harm k  (definitional)
  -- RHS second: fsum (shift (k+1)) (k+1) = fsum (shift (k+1)) k + harm ((k+1)+k)
  have hRfst : fsum (harmTerm B hB) (k + 1)
      = fsum (harmTerm B hB) k + harmTerm B hB k := rfl
  have hRsnd : fsum (fun i => harmTerm B hB ((k + 1) + i)) (k + 1)
      = fsum (fun i => harmTerm B hB ((k + 1) + i)) k
        + harmTerm B hB ((k + 1) + k) := rfl
  rw [hRfst, hRsnd]
  have hbridge :
      (fsum (fun i => harmTerm B hB (k + i)) k + harmTerm B hB (k + k)).eqv
        (harmTerm B hB k + fsum (fun i => harmTerm B hB ((k + 1) + i)) k) :=
    harm_block_reindex B hB k
  -- replace fsum harm (k+k) by (A + Sblk) via ih
  have e1 : (fsum (harmTerm B hB) (k + k) + harmTerm B hB (k + k)
        + harmTerm B hB ((k + k) + 1)).eqv
      (((fsum (harmTerm B hB) k + fsum (fun i => harmTerm B hB (k + i)) k)
          + harmTerm B hB (k + k)) + harmTerm B hB ((k + k) + 1)) :=
    Q'.add_eqv_congr_right _ _ (harmTerm B hB ((k + k) + 1))
      (Q'.add_eqv_congr_right _ _ (harmTerm B hB (k + k)) ih)
  -- ((A + Sblk) + t0) ≃ A + (Sblk + t0) ≃ A + (harm k + blk') ≃ (A + harm k) + blk'
  have e2 : (((fsum (harmTerm B hB) k + fsum (fun i => harmTerm B hB (k + i)) k)
          + harmTerm B hB (k + k))).eqv
      ((fsum (harmTerm B hB) k + harmTerm B hB k)
        + fsum (fun i => harmTerm B hB ((k + 1) + i)) k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (fsum (harmTerm B hB) k)
        (fsum (fun i => harmTerm B hB (k + i)) k) (harmTerm B hB (k + k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (fsum (harmTerm B hB) k) _ _ hbridge) ?_
    exact Q'.eqv_symm (Q'.add_assoc_eqv (fsum (harmTerm B hB) k) (harmTerm B hB k)
      (fsum (fun i => harmTerm B hB ((k + 1) + i)) k))
  -- t1 = harm ((k+k)+1) = harm ((k+1)+k) (index equality)
  have hidxt : (k + k) + 1 = (k + 1) + k := by omega
  refine Q'.eqv_trans _ _ _ e1 ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (harmTerm B hB ((k + k) + 1)) e2) ?_
  rw [hidxt]
  exact Q'.add_assoc_eqv (fsum (harmTerm B hB) k + harmTerm B hB k)
    (fsum (fun i => harmTerm B hB ((k + 1) + i)) k)
    (harmTerm B hB ((k + 1) + k))

/-- `fsum (harmTerm) (2*m) ≃ fsum (harmTerm) m + fsum (shifted block) m`:
the prefix at `2m` splits into the first `m` terms and the block `[m,2m)`. -/
theorem harm_split (B : Q') (hB : (0 : Q') < B) (m : Nat) :
    (fsum (harmTerm B hB) (m + m)).eqv
      (fsum (harmTerm B hB) m
        + fsum (fun i => harmTerm B hB (m + i)) m) := by
  induction m with
  | zero =>
    show (fsum (harmTerm B hB) 0).eqv
      (fsum (harmTerm B hB) 0 + fsum (fun i => harmTerm B hB (0 + i)) 0)
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (fsum (harmTerm B hB) 0)))
  | succ k ih =>
    have hidx : (k + 1) + (k + 1) = (k + k) + 1 + 1 := by omega
    rw [hidx]
    show (fsum (harmTerm B hB) (k + k) + harmTerm B hB (k + k)
            + harmTerm B hB ((k + k) + 1)).eqv
        (fsum (harmTerm B hB) (k + 1)
          + fsum (fun i => harmTerm B hB ((k + 1) + i)) (k + 1))
    exact harm_split_succ B hB k ih

/-! ## 4. The block contributes at least `1/3` once `B ≤ ofNat m`

The block `[m, 2m)` of harmonic terms has `m` entries, each `≥ 1/(2m+B)` (the
last one), so the block sum is `≥ m·1/(2m+B)`.  When `B ≤ ofNat m`, the
denominator `2m + B ≤ 3m`, so `m·1/(2m+B) ≥ m·1/(3m) ≥ 1/3` (cross-multiplied:
`3·m ≥ (2m+B)` and `1·(2m+B) ... `).  We prove `third ≤ block sum`. -/

/-- `third ≤ ofNat m · harmTerm B (2m)` once `1 ≤ m` and `B ≤ ofNat m`.
Cross-multiplied form of `1/3 ≤ m/(2m+B)`, i.e. `2m + B ≤ 3m`. -/
theorem third_le_block_min {B : Q'} (hB : (0 : Q') < B) (m : Nat)
    (_hm : 1 ≤ m) (hBm : B ≤ Q'.ofNat m) :
    third ≤ Q'.ofNat m * harmTerm B hB (m + m) := by
  -- harmTerm B hB (m+m) = divPos 1 (harmDen B (m+m)) h.
  -- ofNat m * divPos 1 D h = divPos (ofNat m) D h  (scalar)... we instead use
  -- le_divPos_of_mul_le-style reasoning at the product level.
  -- It suffices: third * harmDen B (m+m) ≤ ofNat m   AND
  --   (ofNat m * harmTerm) * harmDen ≃ ofNat m. Then combine via cancellation.
  -- Cleaner: show  third ≤ ofNat m * harmTerm, by
  --   third * (harmDen B (m+m)) ≤ ofNat m * (harmTerm * harmDen) ≃ ofNat m.
  -- Step A: ofNat m * (harmTerm * harmDen) ≃ ofNat m.
  have hcancel : (Q'.ofNat m * (harmTerm B hB (m + m) * harmDen B (m + m))).eqv
      (Q'.ofNat m) := by
    have h1 : (harmTerm B hB (m + m) * harmDen B (m + m)).eqv 1 :=
      Q'.divPos_mul_eqv 1 (harmDen B (m + m)) (harmDen_pos hB (m + m))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat m) _ _ h1) ?_
    exact Q'.mul_one_eqv (Q'.ofNat m)
  -- Step B: third * harmDen B (m+m) ≤ ofNat m.
  --   third = divPos 1 (ofNat 3); third * (2m+B) ≤ ofNat m
  --   ⟺ (cross) 1·(... ) : use divPos_le_of_le_mul-form.
  --   third * D ≤ ofNat m  ⟸  D ≤ ofNat m * ofNat 3   [since third = 1/3, mult
  --   both sides by 3]. We prove: third * D ≤ ofNat m via
  --   third * D ≤ third * (ofNat m * ofNat 3) ≃ ofNat m.
  have hD_le : harmDen B (m + m) ≤ Q'.ofNat m * Q'.ofNat 3 := by
    -- harmDen B (m+m) = ofNat (m+m) + B ≤ ofNat (m+m) + ofNat m = ofNat (3m)
    --   ≃ ofNat m * ofNat 3.
    show Q'.ofNat (m + m) + B ≤ Q'.ofNat m * Q'.ofNat 3
    -- ofNat (m+m) + B ≤ ofNat (m+m) + ofNat m
    have hstep1 : Q'.ofNat (m + m) + B ≤ Q'.ofNat (m + m) + Q'.ofNat m :=
      Q'.add_le_add_left _ _ _ hBm
    -- ofNat (m+m) + ofNat m ≃ ofNat (m+m+m) = ofNat (3m) ≃ ofNat m * ofNat 3
    have hstep2 : (Q'.ofNat (m + m) + Q'.ofNat m).eqv (Q'.ofNat m * Q'.ofNat 3) := by
      -- ofNat (m+m) + ofNat m ≃ ofNat ((m+m)+m) = ofNat (m*3)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ofNat_add_eqv (m + m) m)) ?_
      have hnat : (m + m) + m = m * 3 := by omega
      rw [hnat]
      exact ofNat_mul_eqv m 3
    exact Q'.le_trans' _ _ _ hstep1 (Q'.le_of_eqv hstep2)
  have hthird_nonneg : (0 : Q') ≤ third := Q'.le_of_lt third_pos
  have hB1 : third * harmDen B (m + m) ≤ third * (Q'.ofNat m * Q'.ofNat 3) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hD_le hthird_nonneg
  -- third * (ofNat m * ofNat 3) ≃ ofNat m * (third * ofNat 3) ≃ ofNat m * 1 ≃ ofNat m
  have hthird3 : (third * Q'.ofNat 3).eqv 1 :=
    Q'.divPos_mul_eqv 1 (Q'.ofNat 3) (by decide)
  have hB2 : (third * (Q'.ofNat m * Q'.ofNat 3)).eqv (Q'.ofNat m) := by
    -- third * (m * 3) ≃ (third * 3)*m? rather: ≃ m * (third*3) ≃ m*1 ≃ m
    -- third*(m*3) ≃ third*(3*m) ≃ (third*3)*m ≃ 1*m ≃ m
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left third _ _ (Q'.mul_comm_eqv (Q'.ofNat m) (Q'.ofNat 3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv third (Q'.ofNat 3) (Q'.ofNat m))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (Q'.ofNat m) hthird3) ?_
    exact Q'.one_mul_eqv (Q'.ofNat m)
  have hB3 : third * harmDen B (m + m) ≤ Q'.ofNat m :=
    Q'.le_trans' _ _ _ hB1 (Q'.le_of_eqv hB2)
  -- Step C: combine. third ≤ ofNat m * harmTerm.
  -- We have third * D ≤ ofNat m ≃ ofNat m * (harmTerm * D) = (ofNat m * harmTerm)*D.
  -- So third * D ≤ (ofNat m * harmTerm) * D ; cancel D>0.
  have hDpos : (0 : Q') < harmDen B (m + m) := harmDen_pos hB (m + m)
  -- rewrite ofNat m ≃ (ofNat m * harmTerm) * D
  have hRHSeq : (Q'.ofNat m).eqv
      ((Q'.ofNat m * harmTerm B hB (m + m)) * harmDen B (m + m)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat m) (harmTerm B hB (m + m))
      (harmDen B (m + m)))
  have hB4 : third * harmDen B (m + m)
      ≤ (Q'.ofNat m * harmTerm B hB (m + m)) * harmDen B (m + m) :=
    Q'.le_trans' _ _ _ hB3 (Q'.le_of_eqv hRHSeq)
  -- cancel the positive D on the right: a*D ≤ b*D, D>0 ⟹ a ≤ b.
  exact q_le_of_mul_le_mul_right _ _ _ hDpos hB4

/-- **The doubling step.**  For `1 ≤ m` and `B ≤ ofNat m`, the prefix sum at
`2m` exceeds the prefix sum at `m` by at least `1/3`:

    third + harmSum B m  ≤  harmSum B (2m). -/
theorem harm_doubling_step {B : Q'} (hB : (0 : Q') < B) (m : Nat)
    (hm : 1 ≤ m) (hBm : B ≤ Q'.ofNat m) :
    third + harmSum B hB m ≤ harmSum B hB (m + m) := by
  -- harmSum B (m+m) ≃ harmSum B m + block, block = ∑_{i<m} harm (m+i).
  -- block ≥ ofNat m · harm (m+m) ≥ third.
  have hsplit : (harmSum B hB (m + m)).eqv
      (harmSum B hB m + fsum (fun i => harmTerm B hB (m + i)) m) :=
    harm_split B hB m
  -- block lower bound (antitone harmTerm):
  have hblk : Q'.ofNat m * harmTerm B hB (m + m)
      ≤ fsum (fun i => harmTerm B hB (m + i)) m :=
    block_lower_bound (fun {i j} h => harmTerm_anti hB h) m m
  have hthird_blk : third ≤ fsum (fun i => harmTerm B hB (m + i)) m :=
    Q'.le_trans' _ _ _ (third_le_block_min hB m hm hBm) hblk
  -- third + harmSum m ≤ harmSum m + block ≃ harmSum (m+m).
  -- third + harmSum m ≤ block + harmSum m  (add block≥third on left side)
  have hstep : third + harmSum B hB m
      ≤ fsum (fun i => harmTerm B hB (m + i)) m + harmSum B hB m :=
    Q'.add_le_add_right _ _ (harmSum B hB m) hthird_blk
  -- block + harmSum m ≃ harmSum m + block ≃ harmSum (m+m)
  have hcomm : (fsum (fun i => harmTerm B hB (m + i)) m + harmSum B hB m).eqv
      (harmSum B hB (m + m)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv (fsum (fun i => harmTerm B hB (m + i)) m) (harmSum B hB m)) ?_
    exact Q'.eqv_symm hsplit
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcomm)

/-! ## 5. The harmonic divergence — the PROVED diagnostic

Iterating the doubling step from a base `m₀` with `B ≤ ofNat m₀` and `m₀ ≥ 1`:
after `J` doublings the index is `m₀ · 2^J` and the sum is `≥ J · third`.  Since
`J · third` exceeds any `M` (take `J` large), the partial sums of `1/(k+B)` are
unbounded.  The explicit witness `N(M)` is `m₀ · 2^{J(M)}` with `J(M)` chosen so
that `J(M)·third ≥ M`. -/

/-- The base index `m₀(B) = max 1 (B.num.toNat)`: satisfies `1 ≤ m₀` and
`B ≤ ofNat m₀`. -/
def baseIdx (B : Q') : Nat := Nat.max 1 B.num.toNat

theorem baseIdx_ge_one (B : Q') : 1 ≤ baseIdx B := Nat.le_max_left 1 _

theorem baseIdx_ge {B : Q'} (hB : (0 : Q') < B) : B ≤ Q'.ofNat (baseIdx B) := by
  -- B ≤ ofNat B.num.toNat ≤ ofNat (max 1 B.num.toNat).
  have h1 : B ≤ Q'.ofNat B.num.toNat := RatNat.le_ofNat_toNat B (Q'.le_of_lt hB)
  have h2 : Q'.ofNat B.num.toNat ≤ Q'.ofNat (baseIdx B) :=
    CReal.ofNat_le_ofNat (Nat.le_max_right 1 B.num.toNat)
  exact Q'.le_trans' _ _ _ h1 h2

/-- The doubling schedule of indices: `idxSeq B 0 = m₀`,
`idxSeq B (J+1) = idxSeq B J + idxSeq B J` (i.e. `m₀ · 2^J`). -/
def idxSeq (B : Q') : Nat → Nat
  | 0 => baseIdx B
  | J + 1 => idxSeq B J + idxSeq B J

theorem idxSeq_ge_one (B : Q') : ∀ J, 1 ≤ idxSeq B J
  | 0 => baseIdx_ge_one B
  | J + 1 => by
    have h := idxSeq_ge_one B J
    show 1 ≤ idxSeq B J + idxSeq B J
    omega

theorem idxSeq_ge_base (B : Q') : ∀ J, baseIdx B ≤ idxSeq B J
  | 0 => Nat.le_refl _
  | J + 1 => by
    have h := idxSeq_ge_base B J
    show baseIdx B ≤ idxSeq B J + idxSeq B J
    have := idxSeq_ge_one B J
    omega

/-- `B ≤ ofNat (idxSeq B J)` for every `J` (the denominator bound is preserved
along the schedule since the index only grows). -/
theorem idxSeq_dom {B : Q'} (hB : (0 : Q') < B) (J : Nat) :
    B ≤ Q'.ofNat (idxSeq B J) :=
  Q'.le_trans' _ _ _ (baseIdx_ge hB) (CReal.ofNat_le_ofNat (idxSeq_ge_base B J))

/-- **The accumulation along the doubling schedule.**  After `J` doublings,
`J · third ≤ ∑_{k < idxSeq B J} 1/(k+B)`. -/
theorem harm_schedule_lb {B : Q'} (hB : (0 : Q') < B) :
    ∀ J, Q'.ofNat J * third ≤ harmSum B hB (idxSeq B J)
  | 0 => by
    -- ofNat 0 * third ≤ harmSum B m₀ ; LHS ≃ 0 ≤ sum (nonneg).
    have hz : (Q'.ofNat 0 * third).eqv 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ third ofNat_zero_eqv)
        (Q'.zero_mul_eqv third)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) (harmSum_nonneg hB (idxSeq B 0))
  | J + 1 => by
    have ih := harm_schedule_lb hB J
    -- harmSum B (idxSeq (J+1)) = harmSum B (m + m) where m = idxSeq B J.
    -- ≥ third + harmSum B m ≥ third + J·third = (J+1)·third.
    have hstep : third + harmSum B hB (idxSeq B J)
        ≤ harmSum B hB (idxSeq B J + idxSeq B J) :=
      harm_doubling_step hB (idxSeq B J) (idxSeq_ge_one B J) (idxSeq_dom hB J)
    -- (J+1)·third ≃ third + J·third ; and third + J·third ≤ third + harmSum.
    have hLeq : (Q'.ofNat (J + 1) * third).eqv (third + Q'.ofNat J * third) := by
      -- ofNat (J+1) ≃ 1 + ofNat J ; (1 + ofNat J)*third ≃ third + ofNat J * third
      have he : (Q'.ofNat (J + 1)).eqv (1 + Q'.ofNat J) := by
        refine Q'.eqv_trans _ _ _ (ofNat_add_eqv J 1) ?_
        -- ofNat J + ofNat 1 ≃ ofNat J + 1 ≃ 1 + ofNat J
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (Q'.ofNat J) (Q'.ofNat 1) 1 (Q'.eqv_of_eq rfl)) ?_
        exact Q'.add_comm_eqv (Q'.ofNat J) 1
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ third he) ?_
      refine Q'.eqv_trans _ _ _ (ExpNeg.add_mul_eqv 1 (Q'.ofNat J) third) ?_
      exact Q'.add_eqv_congr_right _ _ (Q'.ofNat J * third) (Q'.one_mul_eqv third)
    have hmid : third + Q'.ofNat J * third ≤ third + harmSum B hB (idxSeq B J) :=
      Q'.add_le_add_left _ _ _ ih
    -- chain : (J+1)·third ≃ third + J·third ≤ third + harmSum ≤ harmSum(m+m)
    show Q'.ofNat (J + 1) * third ≤ harmSum B hB (idxSeq B J + idxSeq B J)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq)
      (Q'.le_trans' _ _ _ hmid hstep)

/-- A `Nat` count `J` with `M ≤ ofNat J · third` for any `M : Q'`.
`third = 1/3`, so `ofNat J · third = J/3`; choosing `J = 3·(max 0 M.num.toNat)+1`
overshoots `M`.  We use `J := 3 * M.num.toNat + 3` (slack), proved via
`M ≤ ofNat M.num.toNat ≤ ofNat J · third`. -/
def thirdCount (M : Q') : Nat := 3 * M.num.toNat + 3

theorem le_thirdCount_mul {M : Q'} (hM : (0 : Q') ≤ M) :
    M ≤ Q'.ofNat (thirdCount M) * third := by
  -- M ≤ ofNat M.num.toNat  (RatNat) ; and ofNat M.num.toNat ≤ ofNat J · third.
  have h1 : M ≤ Q'.ofNat M.num.toNat := RatNat.le_ofNat_toNat M hM
  -- ofNat M.num.toNat ≤ ofNat J · third  ⟺  3·M.num.toNat ≤ J  (since third=1/3).
  -- ofNat J · third = ofNat (3n+3) · (1/3).  Show ofNat n ≤ ofNat(3n+3)·(1/3).
  -- Cross: ofNat n ≤ ofNat(3n+3)*(1/3) ⟺ ofNat n * 3 ≤ ofNat (3n+3) (mult by 3).
  have h2 : Q'.ofNat M.num.toNat ≤ Q'.ofNat (thirdCount M) * third := by
    have hcross : Q'.ofNat M.num.toNat * Q'.ofNat 3 ≤ Q'.ofNat (thirdCount M) := by
      have e1 : (Q'.ofNat M.num.toNat * Q'.ofNat 3).eqv (Q'.ofNat (M.num.toNat * 3)) :=
        Q'.eqv_symm (ofNat_mul_eqv M.num.toNat 3)
      have hle : Q'.ofNat (M.num.toNat * 3) ≤ Q'.ofNat (thirdCount M) := by
        apply CReal.ofNat_le_ofNat
        show M.num.toNat * 3 ≤ 3 * M.num.toNat + 3
        omega
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) hle
    have h3third : (Q'.ofNat 3 * third).eqv 1 := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 3) third) ?_
      exact Q'.divPos_mul_eqv 1 (Q'.ofNat 3) (by decide)
    have hexp : (Q'.ofNat M.num.toNat).eqv
        ((Q'.ofNat M.num.toNat * Q'.ofNat 3) * third) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv (Q'.ofNat M.num.toNat))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat M.num.toNat) _ _ (Q'.eqv_symm h3third)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat M.num.toNat) (Q'.ofNat 3) third)
    have hmul : (Q'.ofNat M.num.toNat * Q'.ofNat 3) * third
        ≤ Q'.ofNat (thirdCount M) * third :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hcross (Q'.le_of_lt third_pos)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexp) hmul
  exact Q'.le_trans' _ _ _ h1 h2

/-- **HARMONIC DIVERGENCE — the proved diagnostic.**  For every bound `M : Q'`
there is an EXPLICIT prefix length `N` with `M ≤ ∑_{k<N} 1/(k+B)`.  The witness
is `N = idxSeq B (thirdCount M)` (i.e. `m₀ · 2^{J}` with `J = 3·M.num.toNat+3`):
`J` doublings each add at least `1/3`, so the sum is `≥ J·(1/3) ≥ M`.

This returns the witness as DATA (`Σ' N, M ≤ harmSum B hB N`), per AGENTS.md
Rule 2 / Rule 8: the divergence witness is a usable, computed prefix length. -/
def harmonic_diverges {B : Q'} (hB : (0 : Q') < B) (M : Q') :
    Σ' N : Nat, M ≤ harmSum B hB N := by
  refine ⟨idxSeq B (thirdCount M), ?_⟩
  -- Two cases on the sign of M: if M ≤ 0, sum ≥ 0 ≥ M; else use the schedule.
  rcases q_le_or_lt M 0 with hMle | hMpos
  · exact Q'.le_trans' _ _ _ hMle (harmSum_nonneg hB _)
  · have hM0 : (0 : Q') ≤ M := Q'.le_of_lt hMpos
    -- M ≤ ofNat (thirdCount M) * third ≤ harmSum B (idxSeq B (thirdCount M)).
    have h1 : M ≤ Q'.ofNat (thirdCount M) * third := le_thirdCount_mul hM0
    have h2 : Q'.ofNat (thirdCount M) * third
        ≤ harmSum B hB (idxSeq B (thirdCount M)) :=
      harm_schedule_lb hB (thirdCount M)
    exact Q'.le_trans' _ _ _ h1 h2

/-- The Prop-level corollary (unboundedness): no `R` bounds all harmonic partial
sums.  Stated as `∀ R, ∃ N, R < harmSum …` — a genuinely propositional negative
fact (its witness is recovered by `harmonic_diverges`). -/
theorem harmSum_unbounded {B : Q'} (hB : (0 : Q') < B) (R : Q') :
    ∃ N : Nat, R < harmSum B hB N := by
  -- take M = R + 1: harmonic_diverges gives N with R + 1 ≤ harmSum, so R < harmSum.
  obtain ⟨N, hN⟩ := harmonic_diverges hB (R + 1)
  refine ⟨N, ?_⟩
  -- R < R + 1 ≤ harmSum
  have hlt : R < R + 1 := by
    show R.num * ((R + 1).den : Int) < (R + 1).num * (R.den : Int)
    have e1 : ((R + 1).den : Int) = (R.den : Int) := by
      show ((R.den * (1 : Q').den : Nat) : Int) = (R.den : Int)
      have : (1 : Q').den = 1 := rfl
      rw [this, Nat.mul_one]
    have e2 : (R + 1).num = R.num + (R.den : Int) := by
      show R.num * ((1 : Q').den : Int) + (1 : Q').num * (R.den : Int)
          = R.num + (R.den : Int)
      have hd : ((1 : Q').den : Int) = 1 := rfl
      have hn : (1 : Q').num = 1 := rfl
      rw [hd, hn, Int.mul_one, Int.one_mul]
    rw [e1, e2]
    have hdpos : (0 : Int) < (R.den : Int) := by exact_mod_cast R.den_pos
    -- R.num * R.den < (R.num + R.den) * R.den
    have : R.num * (R.den : Int) < (R.num + (R.den : Int)) * (R.den : Int) := by
      have hgrow : R.num * (R.den : Int) + 0 < R.num * (R.den : Int) + (R.den : Int) * (R.den : Int) := by
        have hsq : (0 : Int) < (R.den : Int) * (R.den : Int) := Int.mul_pos hdpos hdpos
        omega
      calc R.num * (R.den : Int)
          = R.num * (R.den : Int) + 0 := by rw [Int.add_zero]
        _ < R.num * (R.den : Int) + (R.den : Int) * (R.den : Int) := hgrow
        _ = (R.num + (R.den : Int)) * (R.den : Int) := by rw [Int.add_mul]
    exact this
  exact lt_of_lt_of_le hlt hN

/-- `1 − (1 − x) ≃ x` in `Q'`. -/
theorem one_sub_one_sub_eqv (x : Q') : ((1 : Q') - (1 - x)).eqv x := by
  -- 1 + -(1 + -x) ≃ 1 + (-1 + x) ≃ (1 + -1) + x ≃ 0 + x ≃ x
  show ((1 : Q') + -(1 + -x)).eqv x
  have e1 : (-(1 + -x)).eqv ((-1 : Q') + x) := by
    have hm1 : (-(1 + -x)).eqv ((-1 : Q') * (1 + -x)) :=
      Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (1 + -x))
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (1 + -x))))
    refine Q'.eqv_trans _ _ _ hm1 ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-1 : Q') 1 (-x)) ?_
    have ha : ((-1 : Q') * 1).eqv (-1 : Q') := Q'.mul_one_eqv (-1 : Q')
    have hb : ((-1 : Q') * (-x)).eqv x := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-1 : Q') x) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv 1 x)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (1 * x)) ?_
      exact Q'.one_mul_eqv x
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((-1:Q')*1) (-1:Q') ((-1:Q')*(-x)) ha)
      (Q'.add_eqv_congr_left (-1:Q') ((-1:Q')*(-x)) x hb)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ e1) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv 1 (-1 : Q') x)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (1 + (-1 : Q')) 0 x (Q'.add_neg_self_eqv 1)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 x) (Q'.eqv_of_eq (Q'.add_zero' x))

/-- `invSucc k · (k + 1) ≃ 1` packaged as `invSucc k · harmDen 1 k ≃ 1`
(`harmDen 1 k = ofNat k + 1`, which matches `1/(k+1)`'s denominator). -/
theorem invSucc_mul_harmDen_one_eqv (k : Nat) :
    (Q'.invSucc k * harmDen 1 k).eqv 1 := by
  show (Q'.invSucc k * (Q'.ofNat k + 1)).eqv 1
  show (Q'.invSucc k * (Q'.ofNat k + 1)).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((Q'.invSucc k * (Q'.ofNat k + 1)).den : Int)
  have hokn : (Q'.ofNat k + 1).num = ((k + 1 : Nat) : Int) := by
    show (Q'.ofNat k).num * ((1 : Q').den : Int) + (1 : Q').num * ((Q'.ofNat k).den : Int)
        = ((k + 1 : Nat) : Int)
    have h1 : (Q'.ofNat k).num = (k : Int) := rfl
    have h2 : ((Q'.ofNat k).den : Int) = 1 := rfl
    have h3 : (1 : Q').num = 1 := rfl
    have h4 : ((1 : Q').den : Int) = 1 := rfl
    rw [h1, h2, h3, h4, Int.mul_one, Int.one_mul]
    push_cast; omega
  have hpn : (Q'.invSucc k * (Q'.ofNat k + 1)).num = ((k + 1 : Nat) : Int) := by
    show (Q'.invSucc k).num * (Q'.ofNat k + 1).num = ((k + 1 : Nat) : Int)
    rw [Q'.invSucc_num, hokn, Int.one_mul]
  have hpd : ((Q'.invSucc k * (Q'.ofNat k + 1)).den : Int) = ((k + 1 : Nat) : Int) := by
    show (((Q'.invSucc k).den * (Q'.ofNat k + 1).den : Nat) : Int) = ((k + 1 : Nat) : Int)
    have hid : (Q'.invSucc k).den = k + 1 := Q'.invSucc_den k
    have hodd : (Q'.ofNat k + 1).den = 1 := by
      show (Q'.ofNat k).den * (1 : Q').den = 1
      have : (Q'.ofNat k).den = 1 := rfl
      have h1 : (1 : Q').den = 1 := rfl
      rw [this, h1]
    rw [hid, hodd, Nat.mul_one]
  rw [hpn, hpd]
  have h4 : ((1 : Q').den : Int) = 1 := rfl
  have h3 : (1 : Q').num = 1 := rfl
  rw [h3, h4, Int.mul_one, Int.one_mul]

/-! ## 6. The AF rate modulus — the NAMED interface (NOT derived)

`AFRateModulus` packages the standard two-loop asymptotic-freedom prediction for
the per-scale margin `1 − w_k` of the heat-kernel weight along the RG trajectory.
The two-loop running gives `1 − w_k ≍ g_k² ≍ 1/k`; we record this as the bound
`1 − w_k ≤ A/(k+B)` (upper rate) and, for the insufficiency diagnostic, the
matching lower rate `A'/(k+B) ≤ 1 − w_k`.  Every modulus is `Type`-level data.
This is the AF PHYSICS INPUT; it is NOT proved here. -/

/-- **The asymptotic-freedom rate modulus (NAMED interface).**  Carries the rate
constants `A, A', B > 0` and the trajectory `w : Nat → Q'` of heat-kernel weights
with `0 ≤ w_k < 1`, together with the TWO-SIDED AF rate prediction

    A'/(k+B)  ≤  1 − w_k  ≤  A/(k+B)      (the two-loop running, `≍ g_k² ≍ 1/k`).

This is the standard asymptotic-freedom trajectory rate, packaged as a
`Type`-level obligation.  It is the AF physics input — NOT derived in this
module.  A concrete inhabitant (`afRateModulus_canonical`) shows the structure is
non-vacuous. -/
structure AFRateModulus : Type where
  /-- Upper-rate constant. -/
  A : Q'
  /-- Lower-rate constant. -/
  A' : Q'
  /-- Denominator offset. -/
  B : Q'
  /-- `A > 0`. -/
  A_pos : (0 : Q') < A
  /-- `A' > 0`. -/
  A'_pos : (0 : Q') < A'
  /-- `B > 0`. -/
  B_pos : (0 : Q') < B
  /-- The per-scale heat-kernel weight trajectory. -/
  w : Nat → Q'
  /-- `0 ≤ w_k`. -/
  w_nonneg : ∀ k, (0 : Q') ≤ w k
  /-- `w_k < 1`. -/
  w_lt_one : ∀ k, w k < 1
  /-- **Upper AF rate:** `1 − w_k ≤ A/(k+B)` (two-loop prediction). -/
  rate_upper : ∀ k, (1 : Q') - w k ≤ Q'.divPos (A) (harmDen B k) (harmDen_pos B_pos k)
  /-- **Lower AF rate:** `A'/(k+B) ≤ 1 − w_k` (matching two-loop lower bound). -/
  rate_lower : ∀ k, Q'.divPos (A') (harmDen B k) (harmDen_pos B_pos k) ≤ (1 : Q') - w k

/-- **A concrete inhabitant** (sanity / non-vacuity).  Take `A = A' = B = 1` and
`w_k := 1 − 1/(k+1)` (so `1 − w_k = 1/(k+1) = invSucc k`).  Then both rates hold
with `1/(k+1) = 1/(k+B)` exactly, and `0 ≤ w_k < 1` since `0 < 1/(k+1) ≤ 1`.
This shows `AFRateModulus` is non-vacuous (it is NOT the 4D AF trajectory — only
a witness that the interface is inhabitable). -/
def afRateModulus_canonical : AFRateModulus where
  A := 1
  A' := 1
  B := 1
  A_pos := by decide
  A'_pos := by decide
  B_pos := by decide
  w := fun k => 1 - Q'.invSucc k
  w_nonneg := by
    intro k
    -- 0 ≤ 1 - invSucc k  ⟺  invSucc k ≤ 1
    show (0 : Q') ≤ 1 - Q'.invSucc k
    have hle : Q'.invSucc k ≤ (1 : Q') := by
      show (Q'.invSucc k).num * ((1 : Q').den : Int) ≤ (1 : Q').num * ((Q'.invSucc k).den : Int)
      rw [Q'.invSucc_num, Q'.invSucc_den]
      show (1 : Int) * (1 : Int) ≤ (1 : Int) * (((k + 1 : Nat)) : Int)
      have : (1 : Int) ≤ ((k + 1 : Nat) : Int) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      rw [Int.one_mul, Int.one_mul]; exact this
    exact Q'.sub_nonneg_of_le hle
  w_lt_one := by
    intro k
    -- 1 - invSucc k < 1  ⟺  0 < invSucc k
    show (1 : Q') - Q'.invSucc k < 1
    -- (1 - invSucc k) < 1 ⟺ 1 - invSucc k - 1 < 0 ... use cross-product directly.
    show ((1 : Q') - Q'.invSucc k).num * ((1 : Q').den : Int)
        < (1 : Q').num * (((1 : Q') - Q'.invSucc k).den : Int)
    -- (1 - invSucc k).num = 1·(invSucc k).den + (-(invSucc k).num)·1 = (k+1) - 1 = k
    -- (1 - invSucc k).den = 1·(invSucc k).den = k+1
    have hn : ((1 : Q') - Q'.invSucc k).num = (k : Int) := by
      show (1 : Q').num * ((-(Q'.invSucc k)).den : Int)
          + (-(Q'.invSucc k)).num * ((1 : Q').den : Int) = (k : Int)
      have hd : ((-(Q'.invSucc k)).den : Int) = ((k + 1 : Nat) : Int) := by
        show (((Q'.invSucc k).den : Nat) : Int) = ((k + 1 : Nat) : Int)
        rw [Q'.invSucc_den]
      have hnn : (-(Q'.invSucc k)).num = (-1 : Int) := by
        show -((Q'.invSucc k).num) = (-1 : Int); rw [Q'.invSucc_num]
      have h1n : (1 : Q').num = 1 := rfl
      have h1d : ((1 : Q').den : Int) = 1 := rfl
      rw [hd, hnn, h1n, h1d, Int.one_mul, Int.mul_one]
      push_cast; omega
    have hdd : (((1 : Q') - Q'.invSucc k).den : Int) = ((k + 1 : Nat) : Int) := by
      show (((1 : Q').den * (-(Q'.invSucc k)).den : Nat) : Int) = ((k + 1 : Nat) : Int)
      have : (1 : Q').den = 1 := rfl
      rw [this, Nat.one_mul]
      show (((-(Q'.invSucc k)).den : Nat) : Int) = ((k + 1 : Nat) : Int)
      show (((Q'.invSucc k).den : Nat) : Int) = ((k + 1 : Nat) : Int)
      rw [Q'.invSucc_den]
    rw [hn, hdd]
    have h1n : (1 : Q').num = 1 := rfl
    have h1d : ((1 : Q').den : Int) = 1 := rfl
    rw [h1n, h1d, Int.mul_one, Int.one_mul]
    -- k < k + 1
    have : (k : Int) < ((k + 1 : Nat) : Int) := by exact_mod_cast Nat.lt_succ_self k
    exact this
  rate_upper := by
    intro k
    -- 1 - w k = 1 - (1 - invSucc k) = invSucc k ; need invSucc k ≤ divPos 1 (k+1) _.
    -- invSucc k = 1/(k+1), divPos 1 (harmDen 1 k) = 1/(k+1) too ⟹ equal.
    show (1 : Q') - (1 - Q'.invSucc k)
        ≤ Q'.divPos 1 (harmDen 1 k) (harmDen_pos (by decide) k)
    -- LHS ≃ invSucc k.
    have hLHS : ((1 : Q') - (1 - Q'.invSucc k)).eqv (Q'.invSucc k) :=
      one_sub_one_sub_eqv (Q'.invSucc k)
    -- invSucc k ≤ divPos 1 (k+1): use le_divPos_of_mul_le with c = invSucc k:
    --   invSucc k * (k+1) ≤ 1.  In fact invSucc k * harmDen 1 k ≃ 1.
    have hdiv : Q'.invSucc k ≤ Q'.divPos 1 (harmDen 1 k) (harmDen_pos (by decide) k) := by
      refine Q'.le_divPos_of_mul_le 1 (harmDen 1 k) (harmDen_pos (by decide) k) ?_
      -- invSucc k * harmDen 1 k ≤ 1, in fact ≃ 1.
      exact Q'.le_of_eqv (invSucc_mul_harmDen_one_eqv k)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) hdiv
  rate_lower := by
    intro k
    show Q'.divPos 1 (harmDen 1 k) (harmDen_pos (by decide) k)
        ≤ (1 : Q') - (1 - Q'.invSucc k)
    have hRHS : ((1 : Q') - (1 - Q'.invSucc k)).eqv (Q'.invSucc k) :=
      one_sub_one_sub_eqv (Q'.invSucc k)
    -- divPos 1 (k+1) ≤ invSucc k : divPos_le_of_le_mul with C = invSucc k:
    --   1 ≤ invSucc k * harmDen 1 k, in fact ≃ 1.
    have hdiv : Q'.divPos 1 (harmDen 1 k) (harmDen_pos (by decide) k) ≤ Q'.invSucc k := by
      refine Q'.divPos_le_of_le_mul 1 (harmDen 1 k) (harmDen_pos (by decide) k) ?_
      exact Q'.ge_of_eqv (invSucc_mul_harmDen_one_eqv k)
    exact Q'.le_trans' _ _ _ hdiv (Q'.ge_of_eqv hRHS)

/-! ## 7. The linear-bound-insufficiency corollary — the SHARP NEGATIVE VERDICT

The bond-moving budget along the trajectory is `∑_k δ(w_k, p) ≤ ∑_k 6p·(1 − w_k)`
(`BondMovingStep.bondMovingDelta_to_zero`).  Under the LOWER AF rate
`A'/(k+B) ≤ 1 − w_k`, the linear budget is bounded BELOW by
`∑_k 6p·A'/(k+B)`, a constant multiple of the divergent harmonic series.  Hence
NO finite `R` bounds the linear partial sums: the LINEAR crack is provably
insufficient for the summability `∑_k δ(w_k,p) < ∞`. -/

/-- The linear per-scale budget term `6p·(1 − w_k)` (the upstream linear modulus
`bondMovingDelta_to_zero` bounds `δ(w_k,p)` by this when `K(p) = 6p`). -/
def linearBudgetTerm (afr : AFRateModulus) (p : Nat) (k : Nat) : Q' :=
  Q'.ofNat (6 * p) * ((1 : Q') - afr.w k)

/-- `A' · (1/D) ≃ A'/D`: `A' * divPos 1 D h ≃ divPos A' D h`. -/
theorem mul_divPos_one_eqv (a D : Q') (h : (0 : Q') < D) :
    (a * Q'.divPos 1 D h).eqv (Q'.divPos a D h) := by
  -- divPos 1 D h = 1 * recipPos D h ; divPos a D h = a * recipPos D h.
  show (a * (1 * Q'.recipPos D h)).eqv (a * Q'.recipPos D h)
  exact Q'.mul_eqv_congr_left a _ _ (Q'.one_mul_eqv (Q'.recipPos D h))

/-- **The linear budget is bounded below by a scaled harmonic term.**  Under the
lower AF rate, `6p·A'/(k+B) ≤ 6p·(1 − w_k)`, i.e.
`(ofNat(6p)·A')·harmTerm B k ≤ linearBudgetTerm`. -/
theorem harmLB_le_linearBudget (afr : AFRateModulus) (p : Nat) (k : Nat) :
    (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos k
      ≤ linearBudgetTerm afr p k := by
  unfold linearBudgetTerm harmTerm
  -- (ofNat 6p · A') · divPos 1 D  ≃  ofNat 6p · (A' · divPos 1 D)
  --   ≃ ofNat 6p · divPos A' D  ≤  ofNat 6p · (1 - w k).
  have hregroup : ((Q'.ofNat (6 * p) * afr.A')
        * Q'.divPos 1 (harmDen afr.B k) (harmDen_pos afr.B_pos k)).eqv
      (Q'.ofNat (6 * p)
        * Q'.divPos afr.A' (harmDen afr.B k) (harmDen_pos afr.B_pos k)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (6 * p)) afr.A'
        (Q'.divPos 1 (harmDen afr.B k) (harmDen_pos afr.B_pos k))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat (6 * p)) _ _
      (mul_divPos_one_eqv afr.A' (harmDen afr.B k) (harmDen_pos afr.B_pos k))
  -- lower rate: divPos A' D ≤ 1 - w k  (the rate_lower field, same proofs)
  have hlow : Q'.divPos afr.A' (harmDen afr.B k) (harmDen_pos afr.B_pos k)
      ≤ (1 : Q') - afr.w k := afr.rate_lower k
  have hmul : Q'.ofNat (6 * p)
        * Q'.divPos afr.A' (harmDen afr.B k) (harmDen_pos afr.B_pos k)
      ≤ Q'.ofNat (6 * p) * ((1 : Q') - afr.w k) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlow (zero_le_ofNat (6 * p))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) hmul

/-- The linear budget partial sum `∑_{k<N} 6p·(1 − w_k)`. -/
def linearBudgetSum (afr : AFRateModulus) (p : Nat) (N : Nat) : Q' :=
  fsum (linearBudgetTerm afr p) N

/-- The scaled-harmonic partial sum `∑_{k<N} (6p·A')·1/(k+B)`. -/
def scaledHarmSum (afr : AFRateModulus) (p : Nat) (N : Nat) : Q' :=
  fsum (fun k => (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos k) N

/-- The scaled-harmonic partial sum is a lower bound for the linear budget sum
(termwise from `harmLB_le_linearBudget`). -/
theorem scaledHarmSum_le_linearBudgetSum (afr : AFRateModulus) (p : Nat) :
    ∀ N, scaledHarmSum afr p N ≤ linearBudgetSum afr p N
  | 0 => Q'.le_refl' _
  | N + 1 => by
    show fsum (fun k => (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos k) N
          + (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos N
        ≤ fsum (linearBudgetTerm afr p) N + linearBudgetTerm afr p N
    exact q_add_le_add
      (scaledHarmSum_le_linearBudgetSum afr p N) (harmLB_le_linearBudget afr p N)

/-- The scaled-harmonic partial sum equals `(6p·A')·harmSum` up to `eqv`
(pulling the constant out of the sum). -/
theorem scaledHarmSum_eqv (afr : AFRateModulus) (p : Nat) :
    ∀ N, (scaledHarmSum afr p N).eqv
      ((Q'.ofNat (6 * p) * afr.A') * harmSum afr.B afr.B_pos N)
  | 0 => by
    -- 0 ≃ c · 0
    show (fsum (fun k => (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos k) 0).eqv
      ((Q'.ofNat (6 * p) * afr.A') * fsum (harmTerm afr.B afr.B_pos) 0)
    exact Q'.eqv_symm (Q'.mul_zero_eqv (Q'.ofNat (6 * p) * afr.A'))
  | N + 1 => by
    have ih := scaledHarmSum_eqv afr p N
    show (fsum (fun k => (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos k) N
            + (Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos N).eqv
        ((Q'.ofNat (6 * p) * afr.A')
          * (fsum (harmTerm afr.B afr.B_pos) N + harmTerm afr.B afr.B_pos N))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _
        ((Q'.ofNat (6 * p) * afr.A') * harmTerm afr.B afr.B_pos N) ih) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat (6 * p) * afr.A')
      (fsum (harmTerm afr.B afr.B_pos) N) (harmTerm afr.B afr.B_pos N))

/-- **`6p·A' > 0`** — the harmonic prefactor is strictly positive when `p ≥ 1`. -/
theorem scale_pos (afr : AFRateModulus) {p : Nat} (hp : 1 ≤ p) :
    (0 : Q') < Q'.ofNat (6 * p) * afr.A' := by
  refine Q'.mul_pos ?_ afr.A'_pos
  -- 0 < ofNat (6p) since 6p ≥ 1
  show (0 : Int) * ((Q'.ofNat (6 * p)).den : Int) < (Q'.ofNat (6 * p)).num * ((0 : Q').den : Int)
  have hnum : (Q'.ofNat (6 * p)).num = ((6 * p : Nat) : Int) := rfl
  have hden0 : ((0 : Q').den : Int) = 1 := rfl
  rw [hnum, hden0, Int.zero_mul, Int.mul_one]
  have : 1 ≤ 6 * p := by omega
  exact_mod_cast this

/-- `a < a + b` when `0 < b` (strict self-grows-under-positive-add).  Proved at
the `Int` cross-product level (mirrors `Q'.add_le_self_of_nonneg`, strict). -/
theorem lt_add_of_pos_right (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) < (a + b).num * (a.den : Int)
  -- (a+b).num = a.num·b.den + b.num·a.den ; (a+b).den = a.den·b.den.
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int)
      < (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) = (a.den : Int) * (b.den : Int) := by
    push_cast; rfl
  rw [hcast]
  -- LHS = a.num·a.den·b.den ; RHS = a.num·b.den·a.den + b.num·a.den·a.den.
  have hadenpos : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have key : (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  -- expand RHS
  have hexpand : (a.num * (b.den : Int) + b.num * (a.den : Int)) * (a.den : Int)
      = a.num * ((a.den : Int) * (b.den : Int))
        + b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int)
        = a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

/-- **THE INSUFFICIENCY VERDICT — the linear crack is not summable.**  For `p ≥ 1`
and any candidate finite budget `R : Q'`, there is a prefix length `N` with
`R < ∑_{k<N} 6p·(1 − w_k)`.  Hence NO `R` bounds the linear partial sums: the
linear bond-moving budget `∑_k 6p·(1 − w_k)` is bounded below by a divergent
scaled harmonic series and therefore CANNOT close the summability
`∑_k δ(w_k, p) < ∞`.  The renormalized quadratic defect `δ_ren ≤ C·(1 − w)²` is
required instead. -/
theorem linear_bound_not_summable (afr : AFRateModulus) {p : Nat} (hp : 1 ≤ p)
    (R : Q') :
    ∃ N : Nat, R < linearBudgetSum afr p N := by
  -- Let c := 6p·A' > 0 and choose M := R/c + 1 so that R < c·M.  Then divergence
  -- gives N with M ≤ harmSum N, so R < c·M ≤ c·harmSum N ≃ scaledHarmSum N ≤
  -- linearBudgetSum N.
  have hc : (0 : Q') < Q'.ofNat (6 * p) * afr.A' := scale_pos afr hp
  obtain ⟨N, hN⟩ := harmonic_diverges afr.B_pos
    (Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc + 1)
  refine ⟨N, ?_⟩
  -- Step 1: R < c·M.
  have hRcM : R < (Q'.ofNat (6 * p) * afr.A')
      * (Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc + 1) := by
    have heq : ((Q'.ofNat (6 * p) * afr.A')
        * (Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc + 1)).eqv
        (R + (Q'.ofNat (6 * p) * afr.A')) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat (6 * p) * afr.A')
        (Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc) 1) ?_
      have hc_div : ((Q'.ofNat (6 * p) * afr.A')
          * Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc).eqv R := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat (6 * p) * afr.A')
          (Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc)) ?_
        exact Q'.divPos_mul_eqv R (Q'.ofNat (6 * p) * afr.A') hc
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ ((Q'.ofNat (6 * p) * afr.A') * 1) hc_div) ?_
      exact Q'.add_eqv_congr_left R _ _ (Q'.mul_one_eqv (Q'.ofNat (6 * p) * afr.A'))
    have hlt : R < R + (Q'.ofNat (6 * p) * afr.A') :=
      lt_add_of_pos_right R (Q'.ofNat (6 * p) * afr.A') hc
    exact lt_of_lt_of_le hlt (Q'.ge_of_eqv heq)
  -- Step 2: c·M ≤ c·harmSum N.
  have hcM_le : (Q'.ofNat (6 * p) * afr.A')
        * (Q'.divPos R (Q'.ofNat (6 * p) * afr.A') hc + 1)
      ≤ (Q'.ofNat (6 * p) * afr.A') * harmSum afr.B afr.B_pos N :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hN (Q'.le_of_lt hc)
  -- Step 3: c·harmSum N ≃ scaledHarmSum N ≤ linearBudgetSum N.
  have hsc_eqv : (scaledHarmSum afr p N).eqv
      ((Q'.ofNat (6 * p) * afr.A') * harmSum afr.B afr.B_pos N) :=
    scaledHarmSum_eqv afr p N
  have hsc_le : scaledHarmSum afr p N ≤ linearBudgetSum afr p N :=
    scaledHarmSum_le_linearBudgetSum afr p N
  have hch1 : R < (Q'.ofNat (6 * p) * afr.A') * harmSum afr.B afr.B_pos N :=
    lt_of_lt_of_le hRcM hcM_le
  have hch2 : (Q'.ofNat (6 * p) * afr.A') * harmSum afr.B afr.B_pos N
      ≤ linearBudgetSum afr p N :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsc_eqv) hsc_le
  exact lt_of_lt_of_le hch1 hch2

end YMGap.Continuum.AFRateCalibration

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFRateCalibration.q_add_le_add
#print axioms YMGap.Continuum.AFRateCalibration.q_le_of_mul_le_mul_right
#print axioms YMGap.Continuum.AFRateCalibration.q_le_or_lt
#print axioms YMGap.Continuum.AFRateCalibration.harmDen_pos
#print axioms YMGap.Continuum.AFRateCalibration.harmTerm_pos
#print axioms YMGap.Continuum.AFRateCalibration.harmSum_nonneg
#print axioms YMGap.Continuum.AFRateCalibration.fsum_le_of_le
#print axioms YMGap.Continuum.AFRateCalibration.block_lower_bound
#print axioms YMGap.Continuum.AFRateCalibration.harmDen_mono
#print axioms YMGap.Continuum.AFRateCalibration.harmTerm_anti
#print axioms YMGap.Continuum.AFRateCalibration.third_pos
#print axioms YMGap.Continuum.AFRateCalibration.fsum_shift_cons
#print axioms YMGap.Continuum.AFRateCalibration.harm_block_reindex
#print axioms YMGap.Continuum.AFRateCalibration.harm_split_succ
#print axioms YMGap.Continuum.AFRateCalibration.harm_split
#print axioms YMGap.Continuum.AFRateCalibration.third_le_block_min
#print axioms YMGap.Continuum.AFRateCalibration.harm_doubling_step
#print axioms YMGap.Continuum.AFRateCalibration.baseIdx_ge
#print axioms YMGap.Continuum.AFRateCalibration.idxSeq_dom
#print axioms YMGap.Continuum.AFRateCalibration.harm_schedule_lb
#print axioms YMGap.Continuum.AFRateCalibration.le_thirdCount_mul
#print axioms YMGap.Continuum.AFRateCalibration.harmonic_diverges
#print axioms YMGap.Continuum.AFRateCalibration.harmSum_unbounded
#print axioms YMGap.Continuum.AFRateCalibration.afRateModulus_canonical
#print axioms YMGap.Continuum.AFRateCalibration.one_sub_one_sub_eqv
#print axioms YMGap.Continuum.AFRateCalibration.invSucc_mul_harmDen_one_eqv
#print axioms YMGap.Continuum.AFRateCalibration.mul_divPos_one_eqv
#print axioms YMGap.Continuum.AFRateCalibration.harmLB_le_linearBudget
#print axioms YMGap.Continuum.AFRateCalibration.scaledHarmSum_le_linearBudgetSum
#print axioms YMGap.Continuum.AFRateCalibration.scaledHarmSum_eqv
#print axioms YMGap.Continuum.AFRateCalibration.scale_pos
#print axioms YMGap.Continuum.AFRateCalibration.lt_add_of_pos_right
#print axioms YMGap.Continuum.AFRateCalibration.linear_bound_not_summable
