/-
`FusionBratteli` — Milestone 13.2, step 1: the DISCRETE (lattice-path)
reformulation of the SU(2) fusion tower.

# The reformulation (why this kills the integral lift)

`hlocalize` / `FusionConvLogConcaveCore` is the p ≥ 2 fusion local-CLT /
log-concavity wall, parked because its faithful formalization seemed to need
a from-scratch constructive-integral layer (the largest single Lean lift in
the 2026-07-05 plan).  The discretization: the SU(2) Bratteli diagram is a
REFLECTED WALK on `ℕ` — `χ_a ⊗ χ_b ⊇ χ_s` iff `s` lies on the Clebsch–Gordan
LADDER `{a+b, a+b−2, …, |a−b|}` — so p-fold fusion multiplicities are
reflected-lattice-path COUNTS, and the log-concavity claims become finite
combinatorics in the spin endpoint (TP₂/Karlin composition or an
LGV-style injection).  No integrals anywhere.

# What is delivered (all PROVED, axiom-clean)

  * `fusionOK_iff_ladder` — the ladder normal form of the in-repo fusion
    indicator: `fusionOK a b s = true ↔ ∃ k ≤ min a b, a + b = s + 2k`.
    This is the exact interface both downstream routes (TP₂ rows; LGV path
    families) consume, replacing the triangle+parity conjunction.
  * `pathCount j p s` — the p-fold reflected-walk count: the number of
    length-`p` walks `0 → s` on `ℕ` whose every step is a legal spin-`j`
    fusion.  THE discrete carrier of the p-fold fusion multiplicity.
  * Kernel-checked sanity anchors: at `j = 1` the return counts are the
    CATALAN numbers (`pathCount 1 (2n) 0 = C_n`: 1, 2, 5) — the ballot-path
    structure that makes the log-concavity claims classical combinatorics.

# What remains open (AGENTS.md Rule 6)

The log-concavity of `pathCount` in `s` (the TP₂ / LGV theorem), its
weighted upgrade to `boxSum`/`bondMovedCoeff`, and the discharge of
`FusionConvLogConcaveCore.cauchyBinet` through it — the 13.2 campaign body.
Nothing here inhabits any frontier type; the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Nat` / `List` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.FusionBratteli

open YMGap.Continuum.BondMovingStep

/-! ## 1. The ladder normal form of the fusion rule -/

/-- **`fusionOK_iff_ladder` (PROVED).**  The SU(2) fusion indicator in
Clebsch–Gordan LADDER form: `s` occurs in `a ⊗ b` iff `a + b = s + 2k` for
some `k ≤ a, k ≤ b` — i.e. `s ∈ {a+b, a+b−2, …, |a−b|}`.  The reflected-walk
step law: from `a`, tensoring with `b` reaches exactly the `b`-ladder around
`a`. -/
theorem fusionOK_iff_ladder (a b s : Nat) :
    fusionOK a b s = true ↔ ∃ k, k ≤ a ∧ k ≤ b ∧ a + b = s + 2 * k := by
  simp only [fusionOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hminmax : (Nat.max a b - Nat.min a b ≤ s) ↔ (a - b ≤ s ∧ b - a ≤ s) := by
    by_cases hab : a ≤ b
    · rw [show Nat.max a b = b by unfold Nat.max; exact if_pos hab,
        show Nat.min a b = a by unfold Nat.min; exact if_pos hab]
      exact ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩
    · rw [show Nat.max a b = a by unfold Nat.max; exact if_neg hab,
        show Nat.min a b = b by unfold Nat.min; exact if_neg hab]
      exact ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩
  rw [hminmax]
  constructor
  · intro h
    obtain ⟨⟨⟨ha, hb⟩, h2⟩, h3⟩ := h
    have hmod : (a + b - s) % 2 = 0 := by omega
    have hdm := Nat.div_add_mod (a + b - s) 2
    exact ⟨(a + b - s) / 2, by omega, by omega, by omega⟩
  · intro h
    obtain ⟨k, hka, hkb, he⟩ := h
    exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩

/-! ## 2. The p-fold reflected-walk count -/

/-- **The p-fold reflected-walk count** `pathCount j p s`: the number of
length-`p` walks `0 → s` on the spin ladder whose every step `a → s'` is a
legal spin-`j` fusion (`fusionOK a j s'`).  Intermediate spins are truncated
at the reachability bound `j·p` (after `p` steps of size `≤ j` no spin
exceeds `j·p`), so the count is a genuine finite `Nat`.  This is the
discrete carrier of the p-fold fusion multiplicity (the Bratteli path
count). -/
def pathCount (j : Nat) : Nat → Nat → Nat
  | 0, s => if s == 0 then 1 else 0
  | p + 1, s =>
      ((List.range (j * p + 1)).map
        (fun a => pathCount j p a * (if fusionOK a j s then 1 else 0))).foldr
        (· + ·) 0

/-! ## 3. Kernel-checked sanity anchors (non-vacuity)

At `j = 1` the walk is the ±1 ballot walk reflected at `0`; the return
counts are the Catalan numbers — the classical structure the 13.2
log-concavity routes (TP₂ rows / LGV injections) are built on. -/

/-- `C₁ = 1`. -/
theorem pathCount_catalan_one : pathCount 1 2 0 = 1 := by decide

/-- `C₂ = 2`. -/
theorem pathCount_catalan_two : pathCount 1 4 0 = 2 := by decide

/-- `C₃ = 5`. -/
theorem pathCount_catalan_three : pathCount 1 6 0 = 5 := by decide

/-- A spin-2 anchor: two-step returns through the `j = 2` ladder
(`0 → 2 → 0`), exactly one path. -/
theorem pathCount_j2_return : pathCount 2 2 0 = 1 := by decide

/-- The endpoint profile at `p = 4`, `j = 1`: counts `(s = 0, 2, 4) =
(2, 3, 1)` — already LOG-CONCAVE in the (even) endpoint (`3² ≥ 2·1`), the
shape of the claim the 13.2 campaign will prove for all `p`. -/
theorem pathCount_profile_p4 :
    pathCount 1 4 0 = 2 ∧ pathCount 1 4 2 = 3 ∧ pathCount 1 4 4 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

end YMGap.Continuum.FusionBratteli

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
#print axioms YMGap.Continuum.FusionBratteli.pathCount_catalan_one
#print axioms YMGap.Continuum.FusionBratteli.pathCount_catalan_two
#print axioms YMGap.Continuum.FusionBratteli.pathCount_catalan_three
#print axioms YMGap.Continuum.FusionBratteli.pathCount_j2_return
#print axioms YMGap.Continuum.FusionBratteli.pathCount_profile_p4
