/-
`KpowParityTP2` — Milestone 13.2, step 4: the p-STEP `j = 1` fusion kernel
is parity-TP₂ for EVERY `p` (the Cauchy–Binet brick iterated), plus an
honest ADJUDICATION of the row-extraction route.

# What is delivered (all PROVED, axiom-clean)

  * `idK` / `idK_TP2` — the identity kernel and its unconditional TP₂;
  * `kpow K R p` — the p-step composed kernel (`kpow (p+1) = K ∘ kpow p`);
  * `nsum_ne_zero` / `kpow_parity` — parity propagation: an occupied p-step
    entry has `(a + s + p) % 2 = 0` (each `j = 1` step flips parity);
  * `pair_exchange_row_j1` — the GENERIC pair-exchange hypothesis for a
    `stepN 1` row kernel against ANY column kernel that is TP₂ on
    even-shift windows: even intermediate shifts use the two TP₂ bricks
    through the scalar core `cross_mul_le`; ODD intermediate shifts vanish
    by row parity (`stepN_parity`) — the same dichotomy as `KernelCB2`,
    refactored kernel-generically;
  * **`kpow_TP2_j1`** — the induction: for every `p` and range `R`, the
    p-step kernel `kpow (stepN 1) R p` satisfies the TP₂ minor inequality
    on every parity-consistent window (`a ≤ a'`, `s ≤ s'`, both shifts
    even).

# ADJUDICATION banked (AGENTS.md Rule 6 / Lakatos discipline)

The earlier hope "extract row log-concavity via kernel symmetry" is
CORRECTED: TP₂-of-the-kernel does NOT by itself yield log-concavity of a
single row (the δ₀-row `pathCount j p ·` is not a 2×2 minor — TP₂ relates
two DISTINCT rows/columns).  The classical propagation of log-concavity
through composition needs either higher-order total positivity or the
translation-invariant (convolution/PF₂) setting, neither of which the
reflected corner kernel provides for free.  The honest routes to the
all-`p` row statement are therefore (i) the explicit ballot-number
formula layer, or (ii) an LGV-style path-pair injection — both finite
combinatorics, neither landed here.  `kpow_TP2_j1` is the correct and
reusable TP₂ payload (two-row comparisons, the ingredient the weighted
`strongCoupling` interlacing consumes); the row wall is NAMED, not faked.

No frontier type is touched; `FusionConvLogConcaveCore` stays open; the
Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.KernelCB2

namespace YMGap.Continuum.KpowParityTP2

open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionParityTP2
open YMGap.Continuum.KernelCB2

/-! ## 1. The identity kernel and the p-step power -/

/-- The identity kernel. -/
def idK (a s : Nat) : Nat := if a = s then 1 else 0

/-- The identity kernel is unconditionally TP₂. -/
theorem idK_TP2 (a a' s s' : Nat) (haa : a ≤ a') (hss : s ≤ s') :
    idK a s' * idK a' s ≤ idK a s * idK a' s' := by
  unfold idK
  by_cases h1 : a = s'
  · by_cases h2 : a' = s
    · have ha : a = s := by omega
      have hb : a' = s' := by omega
      rw [if_pos h1, if_pos h2, if_pos ha, if_pos hb]
      exact Nat.le_refl _
    · rw [if_neg h2, Nat.mul_zero]
      exact Nat.zero_le _
  · rw [if_neg h1, Nat.zero_mul]
    exact Nat.zero_le _

/-- The p-step composed kernel over intermediate range `R`. -/
def kpow (K : Nat → Nat → Nat) (R : Nat) : Nat → Nat → Nat → Nat
  | 0 => idK
  | p + 1 => comp K (kpow K R p) R

/-! ## 2. Parity propagation -/

/-- A nonzero finite sum has a nonzero term. -/
theorem nsum_ne_zero {f : Nat → Nat} :
    ∀ {R}, nsum f R ≠ 0 → ∃ m, m < R ∧ f m ≠ 0
  | 0, h => absurd rfl h
  | R + 1, h => by
      rw [nsum_succ] at h
      by_cases hR : f R = 0
      · have h' : nsum f R ≠ 0 := by omega
        obtain ⟨m, hm, hne⟩ := nsum_ne_zero h'
        exact ⟨m, Nat.lt_succ_of_lt hm, hne⟩
      · exact ⟨R, Nat.lt_succ_self R, hR⟩

/-- **Parity propagation (PROVED):** an occupied p-step `j = 1` entry has
`(a + s + p) % 2 = 0` — each fundamental step flips the parity. -/
theorem kpow_parity (R : Nat) :
    ∀ p a s, kpow (stepN 1) R p a s ≠ 0 → (a + s + p) % 2 = 0
  | 0, a, s, h => by
      unfold kpow idK at h
      by_cases he : a = s
      · omega
      · rw [if_neg he] at h
        exact absurd rfl h
  | p + 1, a, s, h => by
      obtain ⟨m, _, hm⟩ := nsum_ne_zero h
      have hK : stepN 1 a m ≠ 0 := by
        intro h0
        rw [h0, Nat.zero_mul] at hm
        exact hm rfl
      have hk : kpow (stepN 1) R p m s ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hm
        exact hm rfl
      have p1 := stepN_parity a m hK
      have p2 := kpow_parity R p m s hk
      omega

/-! ## 3. The generic pair exchange for a `stepN 1` row kernel -/

/-- **`pair_exchange_row_j1` (PROVED — the kernel-generic exchange).**  For
a `stepN 1` row pair with even shift and ANY column kernel `K2` that is
TP₂ on even-shift intermediate windows, the paired exchange inequality
holds for ALL intermediate pairs: even shifts by the two TP₂ bricks + the
scalar core; odd shifts vanish by row parity. -/
theorem pair_exchange_row_j1 (K2 : Nat → Nat → Nat) (a a' s s' : Nat)
    (haa : a ≤ a') (ha2 : (a' - a) % 2 = 0)
    (hK2 : ∀ m n, m ≤ n → (n - m) % 2 = 0 →
      K2 m s' * K2 n s ≤ K2 m s * K2 n s') :
    ∀ m n, m ≤ n →
      (stepN 1 a m * K2 m s') * (stepN 1 a' n * K2 n s)
        + (stepN 1 a n * K2 n s') * (stepN 1 a' m * K2 m s)
      ≤ (stepN 1 a m * K2 m s) * (stepN 1 a' n * K2 n s')
        + (stepN 1 a n * K2 n s) * (stepN 1 a' m * K2 m s') := by
  intro m n hmn
  by_cases hpar : (n - m) % 2 = 0
  · have h1 : stepN 1 a n * stepN 1 a' m ≤ stepN 1 a m * stepN 1 a' n :=
      stepN_TP2_j1 a a' m n haa hmn ha2 hpar
    have h2 : K2 m s' * K2 n s ≤ K2 m s * K2 n s' := hK2 m n hmn hpar
    have e1 : (stepN 1 a m * K2 m s') * (stepN 1 a' n * K2 n s)
        = (stepN 1 a m * stepN 1 a' n) * (K2 m s' * K2 n s) := by ac_rfl
    have e2 : (stepN 1 a n * K2 n s') * (stepN 1 a' m * K2 m s)
        = (stepN 1 a n * stepN 1 a' m) * (K2 m s * K2 n s') := by ac_rfl
    have e3 : (stepN 1 a m * K2 m s) * (stepN 1 a' n * K2 n s')
        = (stepN 1 a m * stepN 1 a' n) * (K2 m s * K2 n s') := by ac_rfl
    have e4 : (stepN 1 a n * K2 n s) * (stepN 1 a' m * K2 m s')
        = (stepN 1 a n * stepN 1 a' m) * (K2 m s' * K2 n s) := by ac_rfl
    rw [e1, e2, e3, e4]
    exact cross_mul_le h1 h2
  · have hmn2 : ¬ (m % 2 = n % 2) := by omega
    have hx0 : stepN 1 a m * stepN 1 a' n = 0 := by
      by_cases hm : stepN 1 a m = 0
      · rw [hm, Nat.zero_mul]
      · by_cases hn : stepN 1 a' n = 0
        · rw [hn, Nat.mul_zero]
        · have p1 := stepN_parity a m hm
          have p2 := stepN_parity a' n hn
          exact absurd (by omega : m % 2 = n % 2) hmn2
    have hy0 : stepN 1 a n * stepN 1 a' m = 0 := by
      by_cases hm : stepN 1 a n = 0
      · rw [hm, Nat.zero_mul]
      · by_cases hn : stepN 1 a' m = 0
        · rw [hn, Nat.mul_zero]
        · have p1 := stepN_parity a n hm
          have p2 := stepN_parity a' m hn
          exact absurd (by omega : m % 2 = n % 2) hmn2
    have e1 : (stepN 1 a m * K2 m s') * (stepN 1 a' n * K2 n s)
        = (stepN 1 a m * stepN 1 a' n) * (K2 m s' * K2 n s) := by ac_rfl
    have e2 : (stepN 1 a n * K2 n s') * (stepN 1 a' m * K2 m s)
        = (stepN 1 a n * stepN 1 a' m) * (K2 m s * K2 n s') := by ac_rfl
    rw [e1, e2, hx0, hy0, Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _

/-! ## 4. THE THEOREM: all-`p` parity-TP₂ -/

/-- **`kpow_TP2_j1` (PROVED — the p-step `j = 1` fusion kernel is
parity-TP₂ for EVERY `p`).**  Induction over the Cauchy–Binet brick: the
base is the identity kernel; the step composes `stepN 1` against the
inductive hypothesis through the generic pair exchange. -/
theorem kpow_TP2_j1 (R : Nat) :
    ∀ p a a' s s', a ≤ a' → s ≤ s' →
      (a' - a) % 2 = 0 → (s' - s) % 2 = 0 →
      kpow (stepN 1) R p a s' * kpow (stepN 1) R p a' s
        ≤ kpow (stepN 1) R p a s * kpow (stepN 1) R p a' s'
  | 0, a, a', s, s', haa, hss, _, _ => idK_TP2 a a' s s' haa hss
  | p + 1, a, a', s, s', haa, hss, ha2, hs2 =>
      comp_TP2 (stepN 1) (kpow (stepN 1) R p) R a a' s s'
        (pair_exchange_row_j1 (kpow (stepN 1) R p) a a' s s' haa ha2
          (fun m n hmn hpar =>
            kpow_TP2_j1 R p m n s s' hmn hss hpar hs2))

end YMGap.Continuum.KpowParityTP2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.KpowParityTP2.idK_TP2
#print axioms YMGap.Continuum.KpowParityTP2.nsum_ne_zero
#print axioms YMGap.Continuum.KpowParityTP2.kpow_parity
#print axioms YMGap.Continuum.KpowParityTP2.pair_exchange_row_j1
#print axioms YMGap.Continuum.KpowParityTP2.kpow_TP2_j1
