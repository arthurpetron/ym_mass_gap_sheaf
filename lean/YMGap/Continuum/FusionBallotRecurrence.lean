/-
`FusionBallotRecurrence` — compile the fundamental SU(2) Bratteli walk from
a range-wide executable sum to its sparse two-neighbour recurrence.

# Why this is the next constructive atom

`FusionBratteli.pathCount` is deliberately executable: every step scans the
whole reachable spin range and tests the Clebsch--Gordan predicate.  That is
good for finite certificates but poor as an induction interface.  For the
fundamental representation (`j = 1`) representation theory says that only
the two neighbours can occur:

    a tensor 1 contains s  iff  s = a + 1 or a = s + 1.

This file proves that fact from the already certified ladder theorem, proves
a generic sparse-sum compiler for the `Nat` range fold, and derives an exact
two-neighbour recurrence for `pathCount 1`.  The result is the computation-
theoretic bridge needed by the ballot-formula/LGV campaign: later inductions
reason about two terms rather than re-evaluating a growing finite scan.

# Honest scope

This is the sparse recurrence and its support theorem.  It does not yet prove
the closed ballot-number formula or the all-step row log-concavity, and it
does not inhabit `FusionConvLogConcaveCore`.  Those remain open.

# Constructive contract

Mathlib-free; pure `Nat` / `List` core.  No `Classical`, `native_decide`,
`sorry`, new axiom, or noncomputable definition.  Every theorem is axiom
gated below.
-/

import YMGap.Continuum.KpowParityTP2

namespace YMGap.Continuum.FusionBallotRecurrence

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.FusionParityTP2
open YMGap.Continuum.KernelCB2

/-! ## 1. The fundamental fusion step is exactly the neighbour relation -/

/-- **Fundamental ladder specialization.**  Tensoring spin index `a` with
the fundamental index `1` reaches exactly `a+1`, and also `a-1` when that
predecessor exists. -/
theorem fusionOK_j1_iff_neighbors (a s : Nat) :
    fusionOK a 1 s = true ↔ s = a + 1 ∨ a = s + 1 := by
  rw [fusionOK_iff_ladder]
  constructor
  · rintro ⟨k, hka, hk1, he⟩
    omega
  · intro h
    rcases h with h | h
    · exact ⟨0, by omega, by omega, by omega⟩
    · exact ⟨1, by omega, by omega, by omega⟩

/-- The `Nat` step kernel is the zero-one indicator of the two neighbours. -/
theorem stepN_j1_eq_neighbor_indicator (a s : Nat) :
    stepN 1 a s = if s = a + 1 ∨ a = s + 1 then 1 else 0 := by
  unfold stepN
  by_cases h : fusionOK a 1 s = true
  · rw [if_pos h, if_pos ((fusionOK_j1_iff_neighbors a s).mp h)]
  · rw [if_neg h, if_neg]
    intro hn
    exact h ((fusionOK_j1_iff_neighbors a s).mpr hn)

/-! ## 2. Compile executable range folds to `nsum` -/

/-- The `List.range`/`map`/`foldr` program used by `pathCount` is the
recursive `nsum` used by the Cauchy--Binet toolkit. -/
private theorem range_map_foldr_eq_nsum_add (f : Nat → Nat) : ∀ R z,
    ((List.range R).map f).foldr (fun a b => a + b) z = nsum f R + z
  | 0, z => by simp
  | R + 1, z => by
      rw [List.range_succ, List.map_append, List.foldr_append]
      simp only [List.map, List.foldr]
      rw [range_map_foldr_eq_nsum_add f R (f R + z), nsum_succ]
      omega

theorem range_map_foldr_eq_nsum (f : Nat → Nat) (R : Nat) :
    ((List.range R).map f).foldr (fun a b => a + b) 0 = nsum f R := by
  rw [range_map_foldr_eq_nsum_add]
  omega

/-! ## 3. The sparse-sum compiler -/

/-- A range sum against the fundamental step kernel contains at most two
terms.  The first Boolean guard selects the predecessor `s-1`; the second
selects the successor `s+1`.  The statement retains the precise finite-range
guards, so it is valid for arbitrary `f` without a support hypothesis. -/
theorem nsum_stepN_j1_sparse (f : Nat → Nat) (R s : Nat) :
    nsum (fun a => f a * stepN 1 a s) R =
      (if 0 < s ∧ s - 1 < R then f (s - 1) else 0) +
      (if s + 1 < R then f (s + 1) else 0) := by
  induction R with
  | zero =>
      simp only [nsum_zero]
      rw [if_neg (by omega : ¬ (0 < s ∧ s - 1 < 0)),
        if_neg (by omega : ¬ s + 1 < 0)]
  | succ R ih =>
      rw [nsum_succ, ih,
        stepN_j1_eq_neighbor_indicator]
      by_cases hrel : s = R + 1 ∨ R = s + 1
      · rcases hrel with hpred | hsucc
        · subst s
          have hnewpred : 0 < R + 1 ∧ R + 1 - 1 < R + 1 := by
            constructor
            · exact Nat.zero_lt_succ R
            · simpa only [Nat.add_sub_cancel] using Nat.lt_succ_self R
          rw [if_neg (by omega : ¬ (0 < R + 1 ∧ R + 1 - 1 < R)),
            if_neg (by omega : ¬ R + 1 + 1 < R),
            if_pos hnewpred,
            if_neg (by omega : ¬ R + 1 + 1 < R + 1),
            if_pos (Or.inl rfl)]
          simp only [Nat.add_sub_cancel]
          omega
        · subst R
          rw [if_neg (by omega : ¬ s + 1 < s + 1),
            if_pos (by omega : s + 1 < s + 1 + 1),
            if_pos (Or.inr rfl)]
          by_cases hs0 : s = 0
          · subst s
            rw [if_neg (by omega : ¬ (0 < 0 ∧ 0 - 1 < 0 + 1)),
              if_neg (by omega : ¬ (0 < 0 ∧ 0 - 1 < 0 + 1 + 1))]
            omega
          · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
            have hpredOld : 0 < s ∧ s - 1 < s + 1 :=
              ⟨hspos, Nat.lt_of_le_of_lt (Nat.sub_le s 1) (Nat.lt_succ_self s)⟩
            have hpredNew : 0 < s ∧ s - 1 < s + 1 + 1 :=
              ⟨hspos, Nat.lt_trans hpredOld.2 (Nat.lt_succ_self (s + 1))⟩
            rw [if_pos hpredOld, if_pos hpredNew]
            omega
      · rw [if_neg hrel, Nat.mul_zero, Nat.add_zero]
        have hpiff :
            (0 < s ∧ s - 1 < R) ↔ (0 < s ∧ s - 1 < R + 1) := by
          constructor
          · rintro ⟨hs, hp⟩
            exact ⟨hs, Nat.lt_succ_of_lt hp⟩
          · rintro ⟨hs, hp⟩
            refine ⟨hs, ?_⟩
            by_cases heq : s - 1 = R
            · exfalso
              apply hrel
              left
              omega
            · omega
        have hniff : (s + 1 < R) ↔ (s + 1 < R + 1) := by
          constructor
          · exact Nat.lt_succ_of_lt
          · intro hn
            by_cases heq : s + 1 = R
            · exact absurd (Or.inr heq.symm) hrel
            · omega
        simp only [hpiff, hniff]

/-! ## 4. Exact recurrence and finite-speed support -/

/-- **Exact sparse recurrence for the executable path count.**  One
fundamental step is the predecessor contribution (when the predecessor is in
the old scan range) plus the successor contribution (when it is in range). -/
theorem pathCount_j1_succ_sparse (p s : Nat) :
    pathCount 1 (p + 1) s =
      (if 0 < s ∧ s - 1 < p + 1 then pathCount 1 p (s - 1) else 0) +
      (if s + 1 < p + 1 then pathCount 1 p (s + 1) else 0) := by
  change
    ((List.range (1 * p + 1)).map
      (fun a => pathCount 1 p a * (if fusionOK a 1 s then 1 else 0))).foldr
        (fun a b => a + b) 0 = _
  rw [range_map_foldr_eq_nsum]
  simpa [stepN] using nsum_stepN_j1_sparse (pathCount 1 p) (p + 1) s

/-- **Finite propagation speed.**  A length-`p` fundamental Bratteli walk
cannot end above spin `p`.  This theorem removes the scan-bound guards from
later ballot inductions. -/
theorem pathCount_j1_eq_zero_of_lt : ∀ p s, p < s → pathCount 1 p s = 0
  | 0, s, h => by
      simp [pathCount, show s ≠ 0 by omega]
  | p + 1, s, h => by
      rw [pathCount_j1_succ_sparse]
      rw [if_neg (by omega : ¬ (0 < s ∧ s - 1 < p + 1)),
        if_neg (by omega : ¬ s + 1 < p + 1)]

/-- Guard-free two-neighbour recurrence.  Truncated predecessor `s-1` is
suppressed at the reflecting wall; out-of-cone successor terms vanish by
finite propagation speed. -/
theorem pathCount_j1_succ (p s : Nat) :
    pathCount 1 (p + 1) s =
      (if s = 0 then 0 else pathCount 1 p (s - 1)) + pathCount 1 p (s + 1) := by
  rw [pathCount_j1_succ_sparse]
  cases s with
  | zero =>
      cases p with
      | zero => decide
      | succ p => simp
  | succ s =>
      simp only [Nat.succ_ne_zero, if_false, Nat.zero_lt_succ,
        Nat.succ_sub_one, true_and]
      by_cases hp : s < p + 1
      · rw [if_pos hp]
        by_cases hn : s + 1 + 1 < p + 1
        · rw [if_pos hn]
        · rw [if_neg hn, pathCount_j1_eq_zero_of_lt p (s + 1 + 1) (by omega),
            Nat.add_zero]
      · rw [if_neg hp, if_neg (by omega : ¬ s + 1 + 1 < p + 1),
          pathCount_j1_eq_zero_of_lt p s (by omega),
          pathCount_j1_eq_zero_of_lt p (s + 1 + 1) (by omega)]

/-! ## 5. Occupied paths lie on the parity support lattice -/

/-- Every occupied length-`p` fundamental path has endpoint parity `p`.
This is derived from the sparse recurrence itself, so the executable
`pathCount` now exposes the same parity invariant as the generic kernel
power `kpow_parity`. -/
theorem pathCount_j1_parity : ∀ p s,
    pathCount 1 p s ≠ 0 → (p + s) % 2 = 0
  | 0, s, h => by
      by_cases hs0 : s = 0
      · subst s
        decide
      · simp [pathCount, hs0] at h
  | p + 1, 0, h => by
      have hr := pathCount_j1_succ p 0
      simp at hr
      rw [hr] at h
      simpa only [Nat.add_zero] using pathCount_j1_parity p 1 h
  | p + 1, s + 1, h => by
      have hr := pathCount_j1_succ p (s + 1)
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one] at hr
      rw [hr] at h
      by_cases hleft : pathCount 1 p s = 0
      · rw [hleft, Nat.zero_add] at h
        have hp := pathCount_j1_parity p (s + 1 + 1) h
        omega
      · have hp := pathCount_j1_parity p s hleft
        omega

/-- The contrapositive support rule: the executable count vanishes off the
parity lattice. -/
theorem pathCount_j1_eq_zero_of_parity_ne (p s : Nat)
    (hpar : (p + s) % 2 ≠ 0) : pathCount 1 p s = 0 := by
  by_cases hzero : pathCount 1 p s = 0
  · exact hzero
  · exact absurd (pathCount_j1_parity p s hzero) hpar

end YMGap.Continuum.FusionBallotRecurrence

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionBallotRecurrence.fusionOK_j1_iff_neighbors
#print axioms YMGap.Continuum.FusionBallotRecurrence.stepN_j1_eq_neighbor_indicator
#print axioms YMGap.Continuum.FusionBallotRecurrence.range_map_foldr_eq_nsum
#print axioms YMGap.Continuum.FusionBallotRecurrence.nsum_stepN_j1_sparse
#print axioms YMGap.Continuum.FusionBallotRecurrence.pathCount_j1_succ_sparse
#print axioms YMGap.Continuum.FusionBallotRecurrence.pathCount_j1_eq_zero_of_lt
#print axioms YMGap.Continuum.FusionBallotRecurrence.pathCount_j1_succ
#print axioms YMGap.Continuum.FusionBallotRecurrence.pathCount_j1_parity
#print axioms YMGap.Continuum.FusionBallotRecurrence.pathCount_j1_eq_zero_of_parity_ne
