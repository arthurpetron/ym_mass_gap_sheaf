/-
Track B / R2 — **ASSEMBLING the FULL additive-erosion budget floor from the
deep-UV `O(1/k²)` tail + the finite strong→weak crossover window.**

# What this module does — and how it sharpens the open content

`additiveErosion_uniform_floor` (`AdditiveErosionAdequacy.lean`) needs a TOTAL
budget bound `∀ k, tailSum δ 0 k ≤ Bδ` (and likewise for `ε`).  The AF deep-UV
result `AFDeepUVSummability.af_defect_invSq` bounds the per-step defect
`δ_k ≤ D·1/(k+1)²` only in the ASYMPTOTIC (one-loop AF) regime — i.e. for
`k ≥ K` (deep UV).  The finite CROSSOVER `k < K` (the strong→weak coupling window)
is a SEPARATE finite sum, NOT controlled by the AF `1/k²` scaling.

This module SPLITS the total budget at the crossover scale `K`:

    tailSum δ 0 k  =  tailSum δ 0 K  +  tailSum δ K (k−K)          (for k ≥ K)
                      └── finite crossover ──┘   └── deep-UV tail ──┘

The finite crossover part is bounded by a NAMED input `Bcross` (the genuine
crossover physics — a finite-range no-gap-closing fact); the deep-UV tail is
bounded by `2·D` via the shifted inverse-square comparison
(`recipSq_tailSum_shift_le_two`, itself a corollary of the additive split +
`recipSq_tailSum_le_two ≤ 2`).  Assembling both gives the TOTAL bound
`tailSum δ 0 k ≤ Bcross + 2·D` at EVERY scale `k` (both `k ≤ K` and `k ≥ K`),
which is exactly the slot `additiveErosion_uniform_floor` consumes.

# What is stated / proved here (axiom-clean; pure `Q'`; Rule 8 Type-level data)

  * `tailSum_split` / `tailSum_split_zero` — `tailSum` additivity:
    `tailSum f N (a+b) ≃ tailSum f N a + tailSum f (N+a) b` (and the `N=0` form).
  * `tailSum_le_of_termwise_window` — windowed monotone comparison (the deep-UV
    bound need only hold on the tail window, not everywhere).
  * `tailSum_mono_len` — partial sums of a nonnegative sequence grow with length.
  * `recipSq_tailSum_shift_le_two` — `Σ_{K ≤ j < K+M} 1/(j+1)² ≤ 2` (shifted tail).
  * `uv_tail_bound` — the deep-UV tail `tailSum δ K M ≤ 2·D` from `δ_k ≤ D/(k+1)²`
    for `k ≥ K` (the tail need not know the crossover).
  * `budget_split_bound` — THE ASSEMBLY: finite-crossover bound `Bcross` + deep-UV
    per-step bound (only for `k ≥ K`) ⟹ `∀ k, tailSum δ 0 k ≤ Bcross + 2·D`.
  * `fullFloor_of_crossover_and_AF` — feeds `budget_split_bound` (for both `δ`, `ε`)
    into `additiveErosion_uniform_floor` under the TOTAL-budget anchor-dominance
    `Bcrossε + 2·Dε < (1 − (Bcrossδ + 2·Dδ))·margin 0`, giving the full positive
    uniform floor `∀ k, margin k ≥ floorWitness > 0`.

# HONEST SCOPE — the NEW open content this split EXPOSES (stated, not closed)

The full floor now depends on TWO strictly-smaller named residuals — the genuine
crossover physics, cleanly separated from the (AF-derived) deep-UV tail:

  (a) **The finite crossover defect sums** `Bcrossδ`, `Bcrossε` — the bounds
      `tailSum δ 0 K ≤ Bcrossδ`, `tailSum ε 0 K ≤ Bcrossε` on the FINITE
      strong→weak coupling window `k < K`.  These are finite-range facts (a finite
      sum of `K` terms), the genuine crossover / no-gap-closing physics, carried
      here as NAMED inputs (`hcross`), never derived — the theorem is false for
      arbitrary `Bcross`, so they are genuine hypotheses (Rule 6a).

  (b) **The total-budget anchor-dominance**
      `Bcrossε + 2·Dε < (1 − (Bcrossδ + 2·Dδ))·margin 0` — requires the TOTAL
      defect `Bcrossδ + 2·Dδ < 1` (the finite crossover plus the deep-UV tail must
      not, together, erode the whole anchor margin).

The deep-UV `1/k²` tail (`2·D` half) is DERIVED (from AF, via `af_defect_invSq`
upstream); this module reduces the total budget to (a)+(b).  It does NOT close the
crossover — the strong→weak window bound is left as the honest residual.
-/

import YMGap.Continuum.NetDriftInvSqBudget

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Continuum.SummableInverseSquare

/-! ## 1. `tailSum` additivity (the split lemma) -/

/-- **`tailSum` additivity** (pure `Q'`, as an `eqv`):
`tailSum f N (a + b) ≃ tailSum f N a + tailSum f (N + a) b`.  Induction on `b`;
the step is one `add_assoc` after re-indexing `N + (a + c) = (N + a) + c`. -/
theorem tailSum_split (f : Nat → Q') (N a : Nat) :
    ∀ b, (tailSum f N (a + b)).eqv (tailSum f N a + tailSum f (N + a) b) := by
  intro b
  induction b with
  | zero =>
    -- `a + 0 = a` and `tailSum f (N+a) 0 = 0`, both defeq.
    show (tailSum f N a).eqv (tailSum f N a + tailSum f (N + a) 0)
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (tailSum f N a)))
  | succ c ih =>
    -- LHS defeq `tailSum f N (a+c) + f (N+(a+c))`; RHS defeq
    -- `tailSum f N a + (tailSum f (N+a) c + f ((N+a)+c))`.
    show (tailSum f N (a + c) + f (N + (a + c))).eqv
         (tailSum f N a + (tailSum f (N + a) c + f ((N + a) + c)))
    rw [show N + (a + c) = (N + a) + c from by omega]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (tailSum f N (a + c))
        (tailSum f N a + tailSum f (N + a) c) (f ((N + a) + c)) ih) ?_
    exact Q'.add_assoc_eqv (tailSum f N a) (tailSum f (N + a) c) (f ((N + a) + c))

/-- The `N = 0` split: `tailSum f 0 (a + b) ≃ tailSum f 0 a + tailSum f a b`. -/
theorem tailSum_split_zero (f : Nat → Q') (a b : Nat) :
    (tailSum f 0 (a + b)).eqv (tailSum f 0 a + tailSum f a b) := by
  have h := tailSum_split f 0 a b
  rw [Nat.zero_add] at h
  exact h

/-! ## 2. Windowed termwise comparison and length-monotonicity -/

/-- **Windowed termwise monotonicity of `tailSum`.**  The per-term bound need only
hold on the window `{N, N+1, …}` (indices `N + j`), not at every index — exactly
what the deep-UV `k ≥ K` bound provides on the tail `tailSum · K M`. -/
theorem tailSum_le_of_termwise_window {a b : Nat → Q'} (N : Nat)
    (h : ∀ j, a (N + j) ≤ b (N + j)) :
    ∀ M, tailSum a N M ≤ tailSum b N M := by
  intro M
  induction M with
  | zero => rw [tailSum_zero, tailSum_zero]; exact Q'.le_refl' 0
  | succ M ih =>
    rw [tailSum_succ, tailSum_succ]
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (a (N + M)) ih)
      (Q'.add_le_add_left _ _ _ (h M))

/-- **Length-monotonicity of a nonnegative partial sum.**  For `k ≤ K`,
`tailSum δ 0 k ≤ tailSum δ 0 K` (the extra `K − k` nonnegative terms only add). -/
theorem tailSum_mono_len (δ : Nat → Q') (hδnn : ∀ k, (0 : Q') ≤ δ k)
    {k K : Nat} (h : k ≤ K) :
    tailSum δ 0 k ≤ tailSum δ 0 K := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le h  -- K = k + M
  have hsplit := tailSum_split_zero δ k M
  have hnn : (0 : Q') ≤ tailSum δ k M := tailSum_nonneg δ hδnn k M
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (tailSum δ 0 k) (tailSum δ k M) hnn)
    (Q'.ge_of_eqv hsplit)

/-! ## 3. The shifted inverse-square tail bound `Σ_{K ≤ j < K+M} 1/(j+1)² ≤ 2` -/

/-- **The shifted inverse-square tail bound.**  The tail `Σ_{j<M} 1/(K+j+1)²` is a
sub-window of `Σ_{j<K+M} 1/(j+1)² ≤ 2`, hence itself `≤ 2`.  Proved by the additive
split at `K` and dropping the (nonnegative) crossover head. -/
theorem recipSq_tailSum_shift_le_two (K M : Nat) :
    tailSum recipSqSucc K M ≤ (2 : Q') := by
  have hsplit := tailSum_split_zero recipSqSucc K M
  have hnn : (0 : Q') ≤ tailSum recipSqSucc 0 K :=
    tailSum_nonneg recipSqSucc recipSqSucc_nonneg 0 K
  -- tailSum recipSqSucc K M ≤ (head + tail) ≃ tailSum recipSqSucc 0 (K+M) ≤ 2.
  have hle1 : tailSum recipSqSucc K M
      ≤ tailSum recipSqSucc 0 K + tailSum recipSqSucc K M :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (tailSum recipSqSucc K M) (tailSum recipSqSucc 0 K) hnn)
      (Q'.le_of_eqv (Q'.add_comm_eqv (tailSum recipSqSucc K M) (tailSum recipSqSucc 0 K)))
  have hle2 : tailSum recipSqSucc 0 K + tailSum recipSqSucc K M
      ≤ tailSum recipSqSucc 0 (K + M) := Q'.ge_of_eqv hsplit
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hle1 hle2)
    (recipSq_tailSum_le_two (K + M))

/-- **The deep-UV tail bound.**  If `δ_k ≤ D·1/(k+1)²` for every `k ≥ K` (`D ≥ 0`),
then every deep-UV tail window is bounded by `2·D`:

    tailSum δ K M  ≤  2·D .

The bound need not hold in the crossover `k < K` — only on the tail window. -/
theorem uv_tail_bound (δ : Nat → Q') (K : Nat) (D : Q') (hD : (0 : Q') ≤ D)
    (hUV : ∀ k, K ≤ k → δ k ≤ D * recipSqSucc k) (M : Nat) :
    tailSum δ K M ≤ 2 * D := by
  have h1 : tailSum δ K M ≤ tailSum (fun j => D * recipSqSucc j) K M :=
    tailSum_le_of_termwise_window K
      (fun j => hUV (K + j) (Nat.le_add_right K j)) M
  have h2 : (tailSum (fun j => D * recipSqSucc j) K M).eqv
      (D * tailSum recipSqSucc K M) :=
    tailSum_const_mul D recipSqSucc K M
  have h3 : D * tailSum recipSqSucc K M ≤ D * (2 : Q') :=
    Q'.mul_le_mul_of_nonneg_left (tailSum recipSqSucc K M) 2 D
      (recipSq_tailSum_shift_le_two K M) hD
  have h4 : (D * (2 : Q')).eqv (2 * D) := Q'.mul_comm_eqv D 2
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2)
      (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv h4)))

/-! ## 4. THE BUDGET SPLIT — total bound from finite crossover + deep-UV tail -/

/-- **`budget_split_bound` — the total budget from the crossover + deep-UV split.**
Given
  * a FINITE crossover bound `hcross : tailSum δ 0 K ≤ Bcross` (the strong→weak
    window `k < K` — a NAMED input, the genuine crossover physics), and
  * the deep-UV per-step bound `hUV : ∀ k, K ≤ k → δ k ≤ D·1/(k+1)²` (from
    `AFDeepUVSummability.af_defect_invSq`, holding only in the asymptotic regime),
the TOTAL partial sum is bounded at EVERY scale:

    ∀ k, tailSum δ 0 k ≤ Bcross + 2·D .

For `k ≤ K` the sum is `≤ Bcross` (length-monotonicity); for `k ≥ K` it splits as
`tailSum δ 0 K + tailSum δ K (k−K) ≤ Bcross + 2·D`.  This is exactly the total
budget slot `additiveErosion_uniform_floor` consumes. -/
theorem budget_split_bound
    (δ : Nat → Q') (K : Nat) (D Bcross : Q')
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hD : (0 : Q') ≤ D)
    (hcross : tailSum δ 0 K ≤ Bcross)
    (hUV : ∀ k, K ≤ k → δ k ≤ D * recipSqSucc k) :
    ∀ k, tailSum δ 0 k ≤ Bcross + 2 * D := by
  intro k
  have h2Dnn : (0 : Q') ≤ 2 * D := Q'.mul_nonneg _ _ (by decide) hD
  rcases Nat.le_total K k with hKk | hkK
  · -- Deep-UV regime `k ≥ K`: split at `K`.
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hKk  -- k = K + M
    have hsplit := tailSum_split_zero δ K M
    have huv : tailSum δ K M ≤ 2 * D := uv_tail_bound δ K D hD hUV M
    have hsum : tailSum δ 0 K + tailSum δ K M ≤ Bcross + 2 * D :=
      Q'.le_trans' _ _ _
        (Q'.add_le_add_right (tailSum δ 0 K) Bcross (tailSum δ K M) hcross)
        (Q'.add_le_add_left Bcross (tailSum δ K M) (2 * D) huv)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) hsum
  · -- Crossover regime `k ≤ K`: dominated by the finite crossover bound.
    have hmono : tailSum δ 0 k ≤ tailSum δ 0 K := tailSum_mono_len δ hδnn hkK
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ hmono hcross)
      (Q'.add_le_self_of_nonneg Bcross (2 * D) h2Dnn)

/-! ## 5. THE FULL FLOOR — crossover + deep-UV tail assembled into the margin floor -/

/-- **`fullFloor_of_crossover_and_AF` — the full positive uniform margin floor from
the finite crossover + the AF deep-UV tail.**  Feeds `budget_split_bound` (for both
`δ` and `ε`) into `additiveErosion_uniform_floor` with total budgets
`Bδ := Bcrossδ + 2·Dδ`, `Bε := Bcrossε + 2·Dε`.  Under the TOTAL-budget
anchor-dominance

    Bcrossε + 2·Dε  <  (1 − (Bcrossδ + 2·Dδ))·margin 0 ,

the margin is uniformly bounded below by the strictly positive floor
`(1 − (Bcrossδ + 2·Dδ))·margin 0 − (Bcrossε + 2·Dε)`.

The deep-UV halves `2·Dδ`, `2·Dε` are AF-derived (upstream); the residual open
content is the finite crossover bounds `Bcrossδ`, `Bcrossε` (named inputs
`hcrossδ`/`hcrossε`) and the total-budget anchor-dominance `hanchor`. -/
theorem fullFloor_of_crossover_and_AF
    (margin δ ε : Nat → Q') (K : Nat) (Dδ Dε Bcrossδ Bcrossε : Q')
    (hstep : ∀ k, (1 - δ k) * margin k - ε k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k)
    (hm0 : (0 : Q') ≤ margin 0)
    (hDδ : (0 : Q') ≤ Dδ) (hDε : (0 : Q') ≤ Dε)
    (hcrossδ : tailSum δ 0 K ≤ Bcrossδ)
    (hcrossε : tailSum ε 0 K ≤ Bcrossε)
    (hUVδ : ∀ k, K ≤ k → δ k ≤ Dδ * recipSqSucc k)
    (hUVε : ∀ k, K ≤ k → ε k ≤ Dε * recipSqSucc k)
    (hanchor : Bcrossε + 2 * Dε < (1 - (Bcrossδ + 2 * Dδ)) * margin 0) :
    ∀ k, (1 - (Bcrossδ + 2 * Dδ)) * margin 0 - (Bcrossε + 2 * Dε) ≤ margin k
       ∧ (0 : Q') < (1 - (Bcrossδ + 2 * Dδ)) * margin 0 - (Bcrossε + 2 * Dε) :=
  additiveErosion_uniform_floor margin δ ε (Bcrossδ + 2 * Dδ) (Bcrossε + 2 * Dε)
    hstep hδnn hδ1 hεnn hm0
    (budget_split_bound δ K Dδ Bcrossδ hδnn hDδ hcrossδ hUVδ)
    (budget_split_bound ε K Dε Bcrossε hεnn hDε hcrossε hUVε)
    hanchor

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.tailSum_split
#print axioms YMGap.Continuum.tailSum_split_zero
#print axioms YMGap.Continuum.tailSum_le_of_termwise_window
#print axioms YMGap.Continuum.tailSum_mono_len
#print axioms YMGap.Continuum.recipSq_tailSum_shift_le_two
#print axioms YMGap.Continuum.uv_tail_bound
#print axioms YMGap.Continuum.budget_split_bound
#print axioms YMGap.Continuum.fullFloor_of_crossover_and_AF
