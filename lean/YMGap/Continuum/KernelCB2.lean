/-
`KernelCB2` — Milestone 13.2, step 3: the 2×2 CAUCHY–BINET COMPOSITION
BRICK (Karlin), in the subtraction-free "cross ≤ diagonal" form, over `Nat`
— and its payoff: the composed (two-step) `j = 1` fusion kernel is
parity-TP₂.

# The brick

For `Nat`-valued kernels, TP₂-at-a-window means `K(a,s')·K(a',s) ≤
K(a,s)·K(a',s')`.  The classical Cauchy–Binet argument says TP₂ composes:
if `K₁`, `K₂` are TP₂ then so is `(K₁∘K₂)(a,s) = Σ_m K₁(a,m)K₂(m,s)`.  The
signed-determinant identity is not needed: the EXCHANGE form suffices —
pair the double-sum terms `(m,n)` and `(n,m)` and compare each pair against
the diagonal pairing via the scalar core (`cross_mul_le`):

    y ≤ x  →  v ≤ u  →  x·v + y·u  ≤  x·u + y·v

(the 2×2 rearrangement inequality; the discrete FKG exchange).  Everything
is finite `Nat` arithmetic: `nsum` recursion, a square-sum border
decomposition (`nsum2_succ`), the pair-exchange sum lemma
(`nsum2_exchange`), and product-of-sums = double sum (`nsum_mul_nsum`).

# The payoff (fusion tower)

`comp_TP2` composes ANY two kernels TP₂ on the relevant windows.  For the
`j = 1` fusion kernel `stepN 1` (unconditionally parity-TP₂,
`FusionParityTP2.stepN_TP2_j1`), the intermediate-index windows come in two
kinds: EVEN shifts (handled by `stepN_TP2_j1`) and ODD shifts — where the
cross products VANISH BY PARITY (`stepN_parity_vanish`: on `a ≡ a' (mod 2)`
an occupied pair forces `m ≡ n (mod 2)`).  Hence the exchange hypothesis
holds for ALL intermediate pairs, and the TWO-STEP kernel is parity-TP₂
(`compStep_TP2_j1`) — the induction step for all-`p` same-parity
log-concavity of the Bratteli path counts (`pathCount`), queued next.

# Honest scope (AGENTS.md Rule 6)

This is the composition BRICK, plus its first application to the two-step
`j = 1` kernel.  NOT yet: the all-`p` iteration, the row-log-concavity
extraction, the weighted (`strongCoupling`) cross-parity interlacing, or
any discharge of `FusionConvLogConcaveCore`.  No frontier type is touched;
the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.FusionParityTP2

namespace YMGap.Continuum.KernelCB2

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionParityTP2

/-! ## 1. The `Nat` finite-sum toolkit -/

/-- `Σ_{i<R} f i` over `Nat`. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | R + 1 => nsum f R + f R

@[simp] theorem nsum_zero (f : Nat → Nat) : nsum f 0 = 0 := rfl

@[simp] theorem nsum_succ (f : Nat → Nat) (R : Nat) :
    nsum f (R + 1) = nsum f R + f R := rfl

theorem nsum_congr {f g : Nat → Nat} (h : ∀ i, f i = g i) :
    ∀ R, nsum f R = nsum g R
  | 0 => rfl
  | R + 1 => by rw [nsum_succ, nsum_succ, nsum_congr h R, h R]

theorem nsum_add (f g : Nat → Nat) :
    ∀ R, nsum (fun i => f i + g i) R = nsum f R + nsum g R
  | 0 => rfl
  | R + 1 => by
      rw [nsum_succ, nsum_succ, nsum_succ, nsum_add f g R]
      omega

theorem nsum_le_nsum {f g : Nat → Nat} :
    ∀ R, (∀ i, i < R → f i ≤ g i) → nsum f R ≤ nsum g R
  | 0, _ => Nat.le_refl 0
  | R + 1, h => by
      rw [nsum_succ, nsum_succ]
      exact Nat.add_le_add
        (nsum_le_nsum R (fun i hi => h i (Nat.lt_succ_of_lt hi)))
        (h R (Nat.lt_succ_self R))

theorem nsum_mul_right (f : Nat → Nat) (c : Nat) :
    ∀ R, nsum (fun i => f i * c) R = nsum f R * c
  | 0 => by rw [nsum_zero, nsum_zero, Nat.zero_mul]
  | R + 1 => by
      rw [nsum_succ, nsum_succ, nsum_mul_right f c R, Nat.add_mul]

theorem nsum_mul_left (g : Nat → Nat) (c : Nat) :
    ∀ R, nsum (fun i => c * g i) R = c * nsum g R
  | 0 => by rw [nsum_zero, nsum_zero, Nat.mul_zero]
  | R + 1 => by
      rw [nsum_succ, nsum_succ, nsum_mul_left g c R, Nat.mul_add]

/-- The square-sum border decomposition:
`Σ_{m,n<R+1} F = Σ_{m,n<R} F + Σ_{m<R} F(m,R) + Σ_{n<R} F(R,n) + F(R,R)`. -/
theorem nsum2_succ (F : Nat → Nat → Nat) (R : Nat) :
    nsum (fun m => nsum (fun n => F m n) (R + 1)) (R + 1)
      = nsum (fun m => nsum (fun n => F m n) R) R
        + nsum (fun m => F m R) R
        + nsum (fun n => F R n) R
        + F R R := by
  rw [nsum_succ, nsum_succ (fun n => F R n) R]
  rw [nsum_congr (f := fun m => nsum (fun n => F m n) (R + 1))
    (g := fun m => nsum (fun n => F m n) R + F m R) (fun m => rfl) R]
  rw [nsum_add]
  omega

/-! ## 2. The scalar exchange core -/

/-- **`cross_mul_le` (PROVED — the 2×2 rearrangement core).**
`y ≤ x → v ≤ u → x·v + y·u ≤ x·u + y·v` (the difference is `(x−y)(u−v)`). -/
theorem cross_mul_le {x y u v : Nat} (hxy : y ≤ x) (huv : v ≤ u) :
    x * v + y * u ≤ x * u + y * v := by
  obtain ⟨d, rfl⟩ : ∃ d, x = y + d := ⟨x - y, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, u = v + e := ⟨u - v, by omega⟩
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-! ## 3. The pair-exchange double-sum lemma -/

/-- **`nsum2_exchange` (PROVED).**  If every unordered pair satisfies the
exchanged inequality `F(m,n) + F(n,m) ≤ G(m,n) + G(n,m)`, the square double
sums compare. -/
theorem nsum2_exchange (F G : Nat → Nat → Nat)
    (hpair : ∀ m n, m ≤ n → F m n + F n m ≤ G m n + G n m) :
    ∀ R, nsum (fun m => nsum (fun n => F m n) R) R
      ≤ nsum (fun m => nsum (fun n => G m n) R) R
  | 0 => Nat.le_refl 0
  | R + 1 => by
      rw [nsum2_succ F R, nsum2_succ G R]
      have hIH := nsum2_exchange F G hpair R
      -- border: Σ_{m<R} (F m R + F R m) ≤ Σ_{m<R} (G m R + G R m)
      have hborder : nsum (fun m => F m R) R + nsum (fun n => F R n) R
          ≤ nsum (fun m => G m R) R + nsum (fun n => G R n) R := by
        rw [← nsum_add (fun m => F m R) (fun m => F R m) R,
          ← nsum_add (fun m => G m R) (fun m => G R m) R]
        exact nsum_le_nsum R (fun m hm => hpair m R (Nat.le_of_lt hm))
      -- corner: F R R ≤ G R R (the pair hypothesis at m = n)
      have hcorner : F R R ≤ G R R := by
        have := hpair R R (Nat.le_refl R)
        omega
      omega

/-! ## 4. Product of sums = double sum, and the composition theorem -/

theorem nsum_mul_nsum (f g : Nat → Nat) :
    ∀ R, nsum f R * nsum g R
      = nsum (fun m => nsum (fun n => f m * g n) R) R
  | 0 => rfl
  | R + 1 => by
      rw [nsum2_succ (fun m n => f m * g n) R,
        ← nsum_mul_nsum f g R,
        nsum_mul_right f (g R) R, nsum_mul_left g (f R) R,
        nsum_succ f R, nsum_succ g R, Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega

/-- The composed kernel `(K₁∘K₂)(a,s) = Σ_{m<R} K₁(a,m)·K₂(m,s)`. -/
def comp (K1 K2 : Nat → Nat → Nat) (R : Nat) (a s : Nat) : Nat :=
  nsum (fun m => K1 a m * K2 m s) R

/-- **`comp_TP2` (PROVED — the Cauchy–Binet/Karlin composition brick).**
If `K₁` is TP₂ in its second index against the row pair `(a, a')` and `K₂`
is TP₂ in its first index against the column pair `(s, s')` — as a PAIRED
exchange hypothesis over intermediate indices — then the composed kernel
satisfies the TP₂ minor inequality at `(a, a') × (s, s')`. -/
theorem comp_TP2 (K1 K2 : Nat → Nat → Nat) (R : Nat) (a a' s s' : Nat)
    (hpair : ∀ m n, m ≤ n →
      (K1 a m * K2 m s') * (K1 a' n * K2 n s)
        + (K1 a n * K2 n s') * (K1 a' m * K2 m s)
      ≤ (K1 a m * K2 m s) * (K1 a' n * K2 n s')
        + (K1 a n * K2 n s) * (K1 a' m * K2 m s')) :
    comp K1 K2 R a s' * comp K1 K2 R a' s
      ≤ comp K1 K2 R a s * comp K1 K2 R a' s' := by
  unfold comp
  rw [nsum_mul_nsum, nsum_mul_nsum]
  exact nsum2_exchange _ _ hpair R

/-! ## 5. The fusion payoff: the two-step `j = 1` kernel is parity-TP₂ -/

/-- Parity forcing: an occupied `j = 1` fusion entry has odd index sum. -/
theorem stepN_parity (a m : Nat) (h : stepN 1 a m ≠ 0) :
    (a + m) % 2 = 1 := by
  unfold stepN at h
  by_cases hf : fusionOK a 1 m = true
  · obtain ⟨k, _, _, he⟩ := (fusionOK_iff_ladder a 1 m).mp hf
    omega
  · rw [if_neg hf] at h
    exact absurd rfl h

/-- The paired-exchange hypothesis for the `j = 1` kernel, ALL intermediate
pairs: even shifts by `stepN_TP2_j1`, odd shifts by parity vanishing. -/
theorem stepN_pair_exchange_j1 (a a' s s' : Nat)
    (haa : a ≤ a') (hss : s ≤ s')
    (ha2 : (a' - a) % 2 = 0) (hs2 : (s' - s) % 2 = 0) :
    ∀ m n, m ≤ n →
      (stepN 1 a m * stepN 1 m s') * (stepN 1 a' n * stepN 1 n s)
        + (stepN 1 a n * stepN 1 n s') * (stepN 1 a' m * stepN 1 m s)
      ≤ (stepN 1 a m * stepN 1 m s) * (stepN 1 a' n * stepN 1 n s')
        + (stepN 1 a n * stepN 1 n s) * (stepN 1 a' m * stepN 1 m s') := by
  intro m n hmn
  by_cases hpar : (n - m) % 2 = 0
  · -- even intermediate shift: the two TP₂ bricks + the scalar exchange
    have h1 : stepN 1 a n * stepN 1 a' m ≤ stepN 1 a m * stepN 1 a' n :=
      stepN_TP2_j1 a a' m n haa hmn ha2 hpar
    have h2 : stepN 1 m s' * stepN 1 n s ≤ stepN 1 m s * stepN 1 n s' :=
      stepN_TP2_j1 m n s s' hmn hss hpar hs2
    have hcore := cross_mul_le h1 h2
    -- rearrange the four-factor products into (rows)·(cols) shape
    have e1 : (stepN 1 a m * stepN 1 m s') * (stepN 1 a' n * stepN 1 n s)
        = (stepN 1 a m * stepN 1 a' n) * (stepN 1 m s' * stepN 1 n s) := by
      ac_rfl
    have e2 : (stepN 1 a n * stepN 1 n s') * (stepN 1 a' m * stepN 1 m s)
        = (stepN 1 a n * stepN 1 a' m) * (stepN 1 m s * stepN 1 n s') := by
      ac_rfl
    have e3 : (stepN 1 a m * stepN 1 m s) * (stepN 1 a' n * stepN 1 n s')
        = (stepN 1 a m * stepN 1 a' n) * (stepN 1 m s * stepN 1 n s') := by
      ac_rfl
    have e4 : (stepN 1 a n * stepN 1 n s) * (stepN 1 a' m * stepN 1 m s')
        = (stepN 1 a n * stepN 1 a' m) * (stepN 1 m s' * stepN 1 n s) := by
      ac_rfl
    rw [e1, e2, e3, e4]
    -- x·v + y·u ≤ x·u + y·v with x,y rows and u,v columns
    exact cross_mul_le h1 h2
  · -- odd intermediate shift: every cross product vanishes by parity
    -- (a ≡ a' mod 2, so an occupied row pair forces m ≡ n mod 2)
    have hx : stepN 1 a m * stepN 1 a' n = 0 ∨ m % 2 = n % 2 := by
      by_cases hm : stepN 1 a m = 0
      · exact Or.inl (by rw [hm, Nat.zero_mul])
      · by_cases hn : stepN 1 a' n = 0
        · exact Or.inl (by rw [hn, Nat.mul_zero])
        · have p1 := stepN_parity a m hm
          have p2 := stepN_parity a' n hn
          exact Or.inr (by omega)
    have hy : stepN 1 a n * stepN 1 a' m = 0 ∨ m % 2 = n % 2 := by
      by_cases hm : stepN 1 a n = 0
      · exact Or.inl (by rw [hm, Nat.zero_mul])
      · by_cases hn : stepN 1 a' m = 0
        · exact Or.inl (by rw [hn, Nat.mul_zero])
        · have p1 := stepN_parity a n hm
          have p2 := stepN_parity a' m hn
          exact Or.inr (by omega)
    have hmn2 : ¬ (m % 2 = n % 2) := by omega
    have hx0 : stepN 1 a m * stepN 1 a' n = 0 := by
      rcases hx with h | h
      · exact h
      · exact absurd h hmn2
    have hy0 : stepN 1 a n * stepN 1 a' m = 0 := by
      rcases hy with h | h
      · exact h
      · exact absurd h hmn2
    -- both LHS terms contain a vanishing row pair
    have e1 : (stepN 1 a m * stepN 1 m s') * (stepN 1 a' n * stepN 1 n s)
        = (stepN 1 a m * stepN 1 a' n) * (stepN 1 m s' * stepN 1 n s) := by
      ac_rfl
    have e2 : (stepN 1 a n * stepN 1 n s') * (stepN 1 a' m * stepN 1 m s)
        = (stepN 1 a n * stepN 1 a' m) * (stepN 1 m s * stepN 1 n s') := by
      ac_rfl
    rw [e1, e2, hx0, hy0, Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _

/-- **`compStep_TP2_j1` (PROVED — the TWO-STEP `j = 1` fusion kernel is
parity-TP₂).**  The Cauchy–Binet brick applied to the fundamental fusion
kernel: for `a ≤ a'`, `s ≤ s'` with both shifts even, and ANY intermediate
range `R`,

    K²(a,s')·K²(a',s) ≤ K²(a,s)·K²(a',s'),   K² := comp (stepN 1) (stepN 1) R.

This is the induction step toward all-`p` same-parity log-concavity of the
Bratteli path counts. -/
theorem compStep_TP2_j1 (R a a' s s' : Nat)
    (haa : a ≤ a') (hss : s ≤ s')
    (ha2 : (a' - a) % 2 = 0) (hs2 : (s' - s) % 2 = 0) :
    comp (stepN 1) (stepN 1) R a s' * comp (stepN 1) (stepN 1) R a' s
      ≤ comp (stepN 1) (stepN 1) R a s * comp (stepN 1) (stepN 1) R a' s' :=
  comp_TP2 (stepN 1) (stepN 1) R a a' s s'
    (stepN_pair_exchange_j1 a a' s s' haa hss ha2 hs2)

end YMGap.Continuum.KernelCB2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.KernelCB2.nsum2_succ
#print axioms YMGap.Continuum.KernelCB2.cross_mul_le
#print axioms YMGap.Continuum.KernelCB2.nsum2_exchange
#print axioms YMGap.Continuum.KernelCB2.nsum_mul_nsum
#print axioms YMGap.Continuum.KernelCB2.comp_TP2
#print axioms YMGap.Continuum.KernelCB2.stepN_parity
#print axioms YMGap.Continuum.KernelCB2.stepN_pair_exchange_j1
#print axioms YMGap.Continuum.KernelCB2.compStep_TP2_j1
