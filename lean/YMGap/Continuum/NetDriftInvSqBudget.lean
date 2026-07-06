/-
Track B / R2 — **DERIVING the additive-erosion budget bounds from the per-step
`O(1/k²)` block-spin defect** — the resolved Clay-core scheme fact.

# What this module does — and how it shrinks the open content

`additiveErosion_uniform_floor` (`AdditiveErosionAdequacy.lean`) proves the positive
uniform floor of the true dimensionless margin FROM the SUMMED budget bounds
`Σ_{j<k} δ_j ≤ Bδ`, `Σ_{j<k} ε_j ≤ Bε` plus anchor-dominance
`Bε < (1 − Bδ)·margin 0`.  It leaves the *summed* budget bounds as hypotheses.

This module DERIVES those summed bounds from the **per-step quadratic scaling**
`δ_k ≤ Dδ·1/(k+1)²`, `ε_k ≤ Dε·1/(k+1)²` — the actual, resolved block-spin scheme
fact (the true defect is `δ_k ~ 1/k²`, summable, NOT the falsified MK-linear `1/k`).
Concretely it proves, entirely in the constructive rationals `Q'` and axiom-clean:

    Σ_{j<k} 1/(j+1)²  ≤  2                    (`recipSq_tailSum_le_two`)

via the telescoping `1/(m)² ≤ 1/(m−1) − 1/m` (`SummableInverseSquare.invSq_le_telescope`)
folded into the single invariant `Σ_{j<M} 1/(j+1)² + P(M) ≤ 2`, with the `j = 0`
term (`= 1`, outside the telescope) absorbed by the anchor value `P(0) = 2`.
Scaling gives the budget bound `Σ_{j<k} δ_j ≤ 2·Dδ` (`invSq_budget_bound`), and
feeding this into the adequacy yields the floor from per-step data alone
(`netDriftFloor_of_invSq`).

The open content is thereby reduced from "the *summed* budget is bounded" to "the
*per-step* defect is `O(1/k²)`" — the directly-derived scheme fact resolved by the
block-spin analysis (`δ_k ~ 1/k²`).

# What is stated / proved here (axiom-clean; Rule 8 Type-level data)

  * `tailSum_le_of_termwise` — reusable monotone comparison of `tailSum` under a
    termwise bound (the load-bearing reduction core).
  * `tailSum_const_mul` — `tailSum (fun j => D·g j) = D·tailSum g` (as `eqv`).
  * `recipSq_tailSum_le_two` — the pure-`Q'` inverse-square partial-sum bound `≤ 2`.
  * `invSq_budget_bound` / `invSq_tailSum_le` — the scaled budget bound `≤ 2·D`.
  * `netDriftFloor_of_invSq` — THE DERIVATION: per-step `O(1/k²)` defect + anchor-
    dominance ⟹ the positive uniform floor (instantiates the adequacy).
  * `TrueMarginRecursionInvSq` — the sharper carrier (a `Type`, DELIBERATELY
    UNINHABITED) carrying the per-step quadratic bounds instead of the summed
    budget; `toSummable`/`toPhysical` derive the rest.

The analytic discharge (the per-step `O(1/k²)` bound for the non-abelian multi-link
4D block-spin margin) is out of scope; the carrier is NOT inhabited here.  The open
content is now the single resolved scheme fact `δ_k ≤ Dδ/(k+1)²`.
-/
import YMGap.Continuum.AdditiveErosionAdequacy

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Continuum.SummableInverseSquare

/-! ## 1. The inverse-square term `1/n²` and its successor form `1/(j+1)²` -/

/-- `1/n²` as a single `Q'`, for `n ≥ 1` (numerator `1`, denominator `n·n`). -/
def recipSq (n : Nat) (hn : 0 < n) : Q' := unit (n * n) (Nat.mul_pos hn hn)

/-- The successor-indexed inverse square `recipSqSucc j = 1/(j+1)²`.  This is the
per-step majorant shape used by the budget bounds (denominator base `1`, so the
`j = 0` term is `1`). -/
def recipSqSucc (j : Nat) : Q' := recipSq (j + 1) (Nat.succ_pos j)

theorem recipSqSucc_nonneg (j : Nat) : (0 : Q') ≤ recipSqSucc j :=
  unit_nonneg ((j + 1) * (j + 1)) (Nat.mul_pos (Nat.succ_pos j) (Nat.succ_pos j))

/-! ## 2. Reusable `tailSum` comparison lemmas -/

/-- **Termwise monotonicity of `tailSum`** (the load-bearing comparison core):
a per-term bound `a j ≤ b j` lifts to every window `tailSum a N M ≤ tailSum b N M`. -/
theorem tailSum_le_of_termwise {a b : Nat → Q'} (h : ∀ j, a j ≤ b j) (N : Nat) :
    ∀ M, tailSum a N M ≤ tailSum b N M := by
  intro M
  induction M with
  | zero => rw [tailSum_zero, tailSum_zero]; exact Q'.le_refl' 0
  | succ M ih =>
    rw [tailSum_succ, tailSum_succ]
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (a (N + M)) ih)
      (Q'.add_le_add_left _ _ _ (h (N + M)))

/-- **Constant factor pulls out of `tailSum`** (as an `eqv`):
`tailSum (fun j => D · g j) N M ≃ D · tailSum g N M`. -/
theorem tailSum_const_mul (D : Q') (g : Nat → Q') (N : Nat) :
    ∀ M, (tailSum (fun j => D * g j) N M).eqv (D * tailSum g N M) := by
  intro M
  induction M with
  | zero =>
    rw [tailSum_zero, tailSum_zero]
    exact Q'.eqv_symm (Q'.mul_zero_eqv D)
  | succ M ih =>
    rw [tailSum_succ, tailSum_succ]
    show (tailSum (fun j => D * g j) N M + D * g (N + M)).eqv
         (D * (tailSum g N M + g (N + M)))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (tailSum (fun j => D * g j) N M)
        (D * tailSum g N M) (D * g (N + M)) ih)
      (Q'.eqv_symm (Q'.mul_add_eqv D (tailSum g N M) (g (N + M))))

/-! ## 3. The inverse-square partial-sum bound `Σ_{j<k} 1/(j+1)² ≤ 2`

The telescoping potential for this series.  Because the telescope
`1/m² ≤ 1/(m−1) − 1/m` fires only for `m ≥ 2`, the `j = 0` term `1/1² = 1` is
outside its range; it is absorbed by the anchor value `P(0) = 2`.  For `M ≥ 1`,
`P(M) = 1/M`, and the per-step telescope closes the invariant. -/

/-- The potential `P(0) = 2`, `P(M+1) = 1/(M+1)`. -/
def invSqPotential : Nat → Q'
  | 0 => (2 : Q')
  | (n + 1) => unit (n + 1) (Nat.succ_pos n)

theorem invSqPotential_nonneg : ∀ M, (0 : Q') ≤ invSqPotential M
  | 0 => by decide
  | (n + 1) => unit_nonneg (n + 1) (Nat.succ_pos n)

/-- **The per-step potential inequality** `1/(M+1)² + P(M+1) ≤ P(M)`.
For `M = 0` this is `1/1² + 1/1 ≤ 2`; for `M = n+1` it is the telescope
`1/(n+2)² + 1/(n+2) ≤ 1/(n+1)`. -/
theorem invSqPotential_step (M : Nat) :
    recipSqSucc M + invSqPotential (M + 1) ≤ invSqPotential M := by
  cases M with
  | zero => decide
  | succ n =>
    -- Goal (defeq): unit ((n+1+1)*(n+1+1)) _ + unit (n+1+1) _ ≤ unit (n+1) _.
    have htel := invSq_le_telescope (n + 1 + 1) (by omega)
    have hstep := Q'.add_le_add_right _ _ (unit (n + 1 + 1) (by omega)) htel
    refine Q'.le_trans' _ _ _ hstep ?_
    -- Collapse `(unit ((n+1+1)-1) − unit (n+1+1)) + unit (n+1+1) ≃ unit ((n+1+1)-1)`.
    have hcollapse :
        ((unit (n + 1 + 1 - 1) (by omega) - unit (n + 1 + 1) (by omega))
          + unit (n + 1 + 1) (by omega)).eqv
          (unit (n + 1 + 1 - 1) (by omega)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (unit (n + 1 + 1 - 1) (by omega))
          (-(unit (n + 1 + 1) (by omega))) (unit (n + 1 + 1) (by omega))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (unit (n + 1 + 1 - 1) (by omega)) _ 0
          (Q'.neg_add_self_eqv (unit (n + 1 + 1) (by omega)))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (unit (n + 1 + 1 - 1) (by omega)))
    exact Q'.le_of_eqv hcollapse

/-- **The telescoping invariant** `Σ_{j<M} 1/(j+1)² + P(M) ≤ 2`. -/
theorem invSqPotential_invariant :
    ∀ M, tailSum recipSqSucc 0 M + invSqPotential M ≤ (2 : Q') := by
  intro M
  induction M with
  | zero =>
    show (0 : Q') + invSqPotential 0 ≤ 2
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.zero_add' 2))
  | succ n ih =>
    rw [tailSum_succ, Nat.zero_add]
    -- goal: (tailSum recipSqSucc 0 n + recipSqSucc n) + invSqPotential (n+1) ≤ 2
    have hassoc :
        ((tailSum recipSqSucc 0 n + recipSqSucc n) + invSqPotential (n + 1)).eqv
          (tailSum recipSqSucc 0 n + (recipSqSucc n + invSqPotential (n + 1))) :=
      Q'.add_assoc_eqv _ _ _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hassoc) ?_
    have hmono :
        tailSum recipSqSucc 0 n + (recipSqSucc n + invSqPotential (n + 1))
          ≤ tailSum recipSqSucc 0 n + invSqPotential n :=
      Q'.add_le_add_left _ _ _ (invSqPotential_step n)
    exact Q'.le_trans' _ _ _ hmono ih

/-- **The inverse-square partial-sum bound** `Σ_{j<M} 1/(j+1)² ≤ 2` (pure `Q'`). -/
theorem recipSq_tailSum_le_two (M : Nat) : tailSum recipSqSucc 0 M ≤ (2 : Q') :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (tailSum recipSqSucc 0 M) (invSqPotential M)
      (invSqPotential_nonneg M))
    (invSqPotential_invariant M)

/-! ## 4. The scaled budget bound `Σ_{j<k} δ_j ≤ 2·D` from the per-step `O(1/k²)` -/

/-- **THE BUDGET BOUND (abstract termwise-comparison form).**  Given `D ≥ 0` and a
per-step majorant `δ_k ≤ D·1/(k+1)²`, every partial sum is bounded by `2·D`:

    Σ_{j<k} δ_j  ≤  2·D .

This is the load-bearing reduction: the summed budget is derived from the per-step
quadratic scaling by monotone comparison + the `≤ 2` inverse-square bound. -/
theorem invSq_budget_bound (D : Q') (hD : (0 : Q') ≤ D) (δ : Nat → Q')
    (hδ : ∀ k, δ k ≤ D * recipSqSucc k) (k : Nat) :
    tailSum δ 0 k ≤ 2 * D := by
  have h1 : tailSum δ 0 k ≤ tailSum (fun j => D * recipSqSucc j) 0 k :=
    tailSum_le_of_termwise hδ 0 k
  have h2 : (tailSum (fun j => D * recipSqSucc j) 0 k).eqv (D * tailSum recipSqSucc 0 k) :=
    tailSum_const_mul D recipSqSucc 0 k
  have h3 : D * tailSum recipSqSucc 0 k ≤ D * (2 : Q') :=
    Q'.mul_le_mul_of_nonneg_left (tailSum recipSqSucc 0 k) 2 D
      (recipSq_tailSum_le_two k) hD
  have h4 : (D * (2 : Q')).eqv (2 * D) := Q'.mul_comm_eqv D 2
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2)
      (Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv h4)))

/-- **The scaled inverse-square partial-sum bound** (specialisation, in the
`recipSq (j+1)` shape): `Σ_{j<k} D·1/(j+1)² ≤ 2·D` for `D ≥ 0`. -/
theorem invSq_tailSum_le (D : Q') (hD : (0 : Q') ≤ D) (k : Nat) :
    tailSum (fun j => D * recipSq (j + 1) (Nat.succ_pos j)) 0 k ≤ 2 * D :=
  invSq_budget_bound D hD _ (fun _ => Q'.le_refl' _) k

/-! ## 5. THE DERIVATION — positive uniform floor from the per-step `O(1/k²)` defect -/

/-- **THE NET-DRIFT FLOOR FROM PER-STEP `O(1/k²)` DATA (pure `Q'`).**  Given the
additive-erosion step law, `δ_k ∈ [0,1]`, `ε_k ≥ 0`, `0 ≤ margin 0`, the per-step
quadratic defect bounds `δ_k ≤ Dδ·1/(k+1)²`, `ε_k ≤ Dε·1/(k+1)²` (`Dδ, Dε ≥ 0`),
and anchor-dominance `2·Dε < (1 − 2·Dδ)·margin 0`, the margin is uniformly bounded
below by the strictly positive floor `(1 − 2·Dδ)·margin 0 − 2·Dε`.

The summed budget bounds required by `additiveErosion_uniform_floor` are DERIVED
here from the per-step scaling via `invSq_budget_bound` (`Bδ := 2·Dδ`,
`Bε := 2·Dε`).  The open content is now the per-step `O(1/k²)` defect — the
resolved block-spin scheme fact. -/
theorem netDriftFloor_of_invSq
    (margin δ ε : Nat → Q') (Dδ Dε : Q')
    (hstep : ∀ k, (1 - δ k) * margin k - ε k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k)
    (hm0 : (0 : Q') ≤ margin 0)
    (hDδ : (0 : Q') ≤ Dδ) (hDε : (0 : Q') ≤ Dε)
    (hδ : ∀ k, δ k ≤ Dδ * recipSqSucc k)
    (hε : ∀ k, ε k ≤ Dε * recipSqSucc k)
    (hanchor : 2 * Dε < (1 - 2 * Dδ) * margin 0) :
    ∀ k, (1 - 2 * Dδ) * margin 0 - 2 * Dε ≤ margin k
       ∧ (0 : Q') < (1 - 2 * Dδ) * margin 0 - 2 * Dε :=
  additiveErosion_uniform_floor margin δ ε (2 * Dδ) (2 * Dε) hstep hδnn hδ1 hεnn hm0
    (invSq_budget_bound Dδ hDδ δ hδ) (invSq_budget_bound Dε hDε ε hε) hanchor

/-! ## 6. The sharper carrier — per-step `O(1/k²)` defect as the elementary data

`TrueMarginRecursionInvSq` carries the same physical objects as
`TrueMarginRecursionSummable` (and passes through its `budget_modulus` summability
witness), but replaces the SUMMED budget split `(Bδ, Bε)` + `anchorDominates` with
the strictly sharper PER-STEP quadratic bounds `hδ_invSq`, `hε_invSq` (`δ_k ≤
Dδ/(k+1)²`, `ε_k ≤ Dε/(k+1)²`) + `anchorDominatesInvSq`.  `toSummable` DERIVES the
summed budget via `invSq_budget_bound`.  DELIBERATELY UNINHABITED here: the
per-step `O(1/k²)` defect for the non-abelian 4D block-spin margin is the resolved
scheme fact still to be discharged for real YM. -/

/-- **THE ADDITIVE-EROSION RECURSION WITH PER-STEP `O(1/k²)` DEFECT (`Type`).**
The summed budget of `TrueMarginRecursionSummable` is replaced by the per-step
quadratic bounds; `toSummable` reconstructs the rest.  UNINHABITED here. -/
structure TrueMarginRecursionInvSq : Type where
  /-- The lattice mass `m_lat(a_k)`. -/
  massLat : Nat → Q'
  /-- The lattice spacing `a_k`. -/
  spacing : Nat → Q'
  /-- The spacing is strictly positive. -/
  spacing_pos : ∀ k, (0 : Q') < spacing k
  /-- The dimensionless margin `m_lat(a_k)/a_k`. -/
  margin : Nat → Q'
  /-- The margin is definitionally the physical ratio. -/
  margin_def : ∀ k, margin k = Q'.divPos (massLat k) (spacing k) (spacing_pos k)
  /-- Per-step multiplicative defect `δ_k`. -/
  δ : Nat → Q'
  /-- Per-step ADDITIVE erosion `ε_k`. -/
  ε : Nat → Q'
  /-- The defect is nonnegative. -/
  δ_nonneg : ∀ k, (0 : Q') ≤ δ k
  /-- The defect does not exceed `1`. -/
  δ_le_one : ∀ k, δ k ≤ (1 : Q')
  /-- The erosion is nonnegative. -/
  ε_nonneg : ∀ k, (0 : Q') ≤ ε k
  /-- **The ADDITIVE-erosion step law.** -/
  step : ∀ k, ((1 : Q') - δ k) * margin k - ε k ≤ margin (k + 1)
  /-- The anchor margin `margin 0` is nonnegative. -/
  margin0_nonneg : (0 : Q') ≤ margin 0
  /-- The tail-modulus constant for the `(δ+ε)` budget. -/
  budgetTailConst : Q'
  /-- **Rule-8.3 explicit tail-rate witness** (mirrors `GradedTowerSummable`). -/
  budget_modulus : ∀ N M,
      tailSum (fun k => δ k + ε k) N M ≤ budgetTailConst * pot 2 (by decide) N
  /-- The per-step quadratic scale `Dδ`. -/
  Dδ : Q'
  /-- The per-step quadratic scale `Dε`. -/
  Dε : Q'
  /-- `Dδ ≥ 0`. -/
  Dδ_nonneg : (0 : Q') ≤ Dδ
  /-- `Dε ≥ 0`. -/
  Dε_nonneg : (0 : Q') ≤ Dε
  /-- **THE PER-STEP `O(1/k²)` DEFECT** `δ_k ≤ Dδ·1/(k+1)²` — the resolved block-spin
  scheme fact (`δ_k ~ 1/k²`, summable), strictly sharper than the summed budget. -/
  hδ_invSq : ∀ k, δ k ≤ Dδ * recipSqSucc k
  /-- **THE PER-STEP `O(1/k²)` EROSION** `ε_k ≤ Dε·1/(k+1)²`. -/
  hε_invSq : ∀ k, ε k ≤ Dε * recipSqSucc k
  /-- **ANCHOR-DOMINATES-BUDGET** in per-step form `2·Dε < (1 − 2·Dδ)·margin 0`. -/
  anchorDominatesInvSq : 2 * Dε < (1 - 2 * Dδ) * margin 0

/-- **DERIVATION BRIDGE.**  A `TrueMarginRecursionInvSq` yields a
`TrueMarginRecursionSummable` whose summed budget split (`Bδ := 2·Dδ`,
`Bε := 2·Dε`) is PROVED from the per-step quadratic bounds via `invSq_budget_bound`,
not asserted. -/
def TrueMarginRecursionInvSq.toSummable
    (T : TrueMarginRecursionInvSq) : TrueMarginRecursionSummable where
  massLat := T.massLat
  spacing := T.spacing
  spacing_pos := T.spacing_pos
  margin := T.margin
  margin_def := T.margin_def
  δ := T.δ
  ε := T.ε
  δ_nonneg := T.δ_nonneg
  δ_le_one := T.δ_le_one
  ε_nonneg := T.ε_nonneg
  step := T.step
  margin0_nonneg := T.margin0_nonneg
  budgetTailConst := T.budgetTailConst
  budget_modulus := T.budget_modulus
  Bδ := 2 * T.Dδ
  Bε := 2 * T.Dε
  budgetSplit_δ := invSq_budget_bound T.Dδ T.Dδ_nonneg T.δ T.hδ_invSq
  budgetSplit_ε := invSq_budget_bound T.Dε T.Dε_nonneg T.ε T.hε_invSq
  anchorDominates := T.anchorDominatesInvSq

/-- A `TrueMarginRecursionInvSq` feeds the whole φ⁴→YM bridge with its positive
continuum limit DERIVED from the per-step `O(1/k²)` defect (via `toSummable` then
`TrueMarginRecursionSummable.toPhysical`). -/
def TrueMarginRecursionInvSq.toPhysical
    (T : TrueMarginRecursionInvSq) : TrueMarginRecursionPhysical :=
  T.toSummable.toPhysical

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.tailSum_le_of_termwise
#print axioms YMGap.Continuum.tailSum_const_mul
#print axioms YMGap.Continuum.recipSq_tailSum_le_two
#print axioms YMGap.Continuum.invSq_budget_bound
#print axioms YMGap.Continuum.invSq_tailSum_le
#print axioms YMGap.Continuum.netDriftFloor_of_invSq
#print axioms YMGap.Continuum.TrueMarginRecursionInvSq.toSummable
#print axioms YMGap.Continuum.TrueMarginRecursionInvSq.toPhysical
