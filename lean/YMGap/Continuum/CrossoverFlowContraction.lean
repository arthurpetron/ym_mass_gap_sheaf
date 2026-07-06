/-
Track B / R2 — the CROSSOVER defect sum as a FLOW-CONTRACTION obligation, and the
COMPLEMENTARITY of the quadratic block-spin defect with the character mechanism.

# What this module does (read first)

`CrossoverAnchorFloor.fullFloor_reduced_to_crossover` reduces the WHOLE 4D SU(N)
continuum margin floor to ONE named obligation `CrossoverWindowDefect δ ε K`: the
finite strong→weak crossover defect sums `Σ_{k<K} δ_k ≤ Bδ`, `Σ_{k<K} ε_k ≤ Bε`,
with the anchor tied to the PROVED strong-coupling gap (`107/108`) and the deep-UV
tail AF-derived.  `RenDefectQuadFactor.bondMovingDeltaRen_le_sixp` proves the
per-step defect is QUADRATIC in the weak-coupling margin:

    δ_k  =  bondMovingDeltaRen N p (w_k)  ≤  6·p·(1 − w_k)² .

This module sharpens the crossover budget `Bcrossδ = Σ_{k<K} 6p(1 − w_k)²` two ways.

## 1. FLOW CONTRACTION ⇒ an EXPLICIT, K-INDEPENDENT crossover budget

Along the RG flow toward the UV the weak-coupling margin `m_k := 1 − w_k` DECREASES
(`w_k → 1`).  If it contracts geometrically, `m_{k+1} ≤ ρ·m_k` with `0 ≤ ρ` and
`ρ² < 1`, then the squared margins `m_k²` contract with rate `t = ρ²`, and the
geometric partial-sum bound gives the K-INDEPENDENT

    Σ_{k<K} m_k²  ≤  m_0² · 1/(1 − ρ²)         (`crossover_sq_sum_le`),
    Σ_{k<K} δ_k   ≤  6p · m_0² · 1/(1 − ρ²)  =:  Bcrossδ   (`crossover_sum_le`).

`crossoverDefect_ofFlowContraction` inhabits the single named obligation
`CrossoverWindowDefect` from this ONE flow-contraction fact (`ρ² < 1`) plus a
per-step additive cap.  So the entire crossover budget is reduced to the geometric
flow-contraction rate `ρ`.  It CONSUMES the contraction hypothesis; nothing is
inhabited unconditionally, so the frontier obligation stays genuinely open.

## 2. COMPLEMENTARITY with the character mechanism (the key leverage)

`δ_k = 6p(1 − w_k)²` is SMALL near `w = 1` — exactly where the character mechanism
FAILS (`rho = 2w³ ≥ 1` at `w ≥ 2^{−1/3}`, `CharacterWindowCeiling`).  So the two
mechanisms have OPPOSITE scaling and are COMPLEMENTARY:

  * CHARACTERS: rate `ρ_char = 2w³ < 1` for `w < 2^{−1/3} ≈ 0.7937` (proved up to the
    rational edge `7/9`, `CharacterWindowCeiling.rho_lt_one_ext`); FAIL above.
  * BLOCK-SPIN: per-step `δ_k = 6p(1 − w_k)²` is `< 1/2` for `w` near `1` (for
    `p = 1`, whenever `1 − w < 1/√12 ≈ 0.289`, i.e. `w > 0.711`), covering the
    character-FAIL region `(2^{−1/3}, 1]`.

At the concrete handoff `w* = 79/100` (below the ceiling, `w*³ < 1/2`) BOTH hold:
`ρ_char(w*) = 2·(79/100)³ < 1` AND the block-spin per-step defect `6·(21/100)² < 1/2`.
`blockspin_perstep_le_handoff` proves the block-spin per-step defect stays `< 1/2`
on the WHOLE tail `[w*, 1]`, unconditionally — so the block-spin per-step controls
the character-fail window.  The SUMMED budget over that window still needs the flow
contraction of §1 (an infinite tail `w → 1` would otherwise diverge); the deep-UV
part is the AF `1/k²` tail (`AFDeepUVSummability`), the finite crossover part is the
`CrossoverWindowDefect`.  `numeric_budget_clears` exhibits a concrete PASSING
instance `Bcrossδ + 2·Dδ < 1/2`.

# HONEST SCOPE (AGENTS.md Rule 6 / Rule 9)

This module does NOT close the continuum gap.  It shows:
  (a) the crossover budget is an EXPLICIT flow-contraction obligation `ρ² < 1`
      (`crossover_sum_le`, `crossoverDefect_ofFlowContraction`), reducing the whole
      floor to that ONE fact (`fullFloor_of_flowContraction`);
  (b) the block-spin per-step defect UNCONDITIONALLY controls the character-fail
      sub-window `(2^{−1/3}, 1]` (`blockspin_perstep_le_handoff`), the opposite
      scaling to characters — a genuine complementary advance at the per-step level;
  (c) a concrete numeric instance where the total budget clears `< 1/2`
      (`numeric_budget_clears`).
The flow-contraction rate `ρ² < 1` is a GENUINE input (the true AF harmonic flow
`m_k ∼ 1/k` has `ρ_k → 1`, so no fixed `ρ < 1` holds in the deep UV; over a FINITE
crossover window it holds with a window-dependent `ρ`).  `CrossoverWindowDefect` is
NEVER inhabited unconditionally.  NO 4D Yang–Mills mass gap is claimed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` core reusing the proved `tailSum` toolkit, `divPos`/`recipPos`
order lemmas, `Q'.pow`, and the `CrossoverWindowDefect` obligation.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.CrossoverAnchorFloor
import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.CrossoverFlowContraction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.CrossoverAnchorFloor

/-! ## 0. Small `Q'` glue -/

/-- `(ρ·a)·(ρ·a) ≃ (ρ·ρ)·(a·a)` — the squared-product regroup. -/
theorem sqProd_regroup (ρ a : Q') :
    ((ρ * a) * (ρ * a)).eqv ((ρ * ρ) * (a * a)) := by
  -- (ρ·a)·(ρ·a) ≃ ρ·(a·(ρ·a)) ≃ ρ·((a·ρ)·a) ≃ ρ·((ρ·a)·a) ≃ ρ·(ρ·(a·a)) ≃ (ρ·ρ)·(a·a)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv ρ a (ρ * a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left ρ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a ρ a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left ρ _ _
      (Q'.mul_eqv_congr_right _ _ a (Q'.mul_comm_eqv a ρ))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left ρ _ _ (Q'.mul_assoc_eqv ρ a a)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv ρ ρ (a * a))

/-- `-(x) ≤ 0` from `0 ≤ x`. -/
theorem neg_nonpos_of_nonneg {x : Q'} (hx : (0 : Q') ≤ x) : -x ≤ (0 : Q') := by
  have h : (0 : Q') + (-x) ≤ x + (-x) := Q'.add_le_add_right 0 x (-x) hx
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_neg_self_eqv x)))
  exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-x)))

/-! ## 1. THE GEOMETRIC PARTIAL-SUM BOUND `Σ_{k<K} t^k ≤ 1/(1 − t)` -/

/-- **The telescoping identity** `(1 − t)·Σ_{k<K} t^k ≃ 1 − t^K`.  Induction on `K`;
the step uses `(1 − t)·t^K ≃ t^K − t^{K+1}` and cancellation `−t^K + t^K ≃ 0`. -/
theorem geomTelescope (t : Q') :
    ∀ K, (((1 : Q') - t) * tailSum (fun k => t ^ k) 0 K).eqv ((1 : Q') - t ^ K) := by
  intro K
  induction K with
  | zero =>
    show (((1 : Q') - t) * tailSum (fun k => t ^ k) 0 0).eqv ((1 : Q') - t ^ 0)
    rw [tailSum_zero]
    refine Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv ((1 : Q') - t)) ?_
    exact Q'.eqv_symm (Q'.add_neg_self_eqv (1 : Q'))
  | succ K ih =>
    show (((1 : Q') - t) * tailSum (fun k => t ^ k) 0 (K + 1)).eqv ((1 : Q') - t ^ (K + 1))
    rw [tailSum_succ, Nat.zero_add]
    -- (1−t)·(S_K + t^K) ≃ (1−t)·S_K + (1−t)·t^K
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv ((1 : Q') - t) (tailSum (fun k => t ^ k) 0 K) (t ^ K)) ?_
    -- ≃ (1 − t^K) + (1−t)·t^K   [ih on the first summand]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (((1 : Q') - t) * t ^ K) ih) ?_
    -- (1−t)·t^K ≃ t^K + −(t·t^K)
    have hB : (((1 : Q') - t) * t ^ K).eqv (t ^ K + -(t * t ^ K)) :=
      Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') (-t) (t ^ K))
        (Q'.add_eqv_congr' (Q'.one_mul_eqv (t ^ K)) (Q'.neg_mul_eqv t (t ^ K)))
    -- rewrite the second summand
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((1 : Q') - t ^ K) _ _ hB) ?_
    -- ((1 + −t^K) + (t^K + −(t·t^K))) ≃ 1 + −(t·t^K)
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (1 : Q') (-(t ^ K)) (t ^ K + -(t * t ^ K))) ?_
    refine Q'.add_eqv_congr_left (1 : Q') _ _ ?_
    -- −t^K + (t^K + −(t·t^K)) ≃ −(t·t^K)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-(t ^ K)) (t ^ K) (-(t * t ^ K)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(t * t ^ K)) (Q'.neg_add_self_eqv (t ^ K))) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-(t * t ^ K)))

/-- `1 − t^K ≤ 1` for `0 ≤ t` (since `t^K ≥ 0`). -/
theorem oneSub_pow_le_one {t : Q'} (ht0 : (0 : Q') ≤ t) (K : Nat) :
    (1 : Q') - t ^ K ≤ (1 : Q') := by
  have hstep : (1 : Q') + -(t ^ K) ≤ (1 : Q') + 0 :=
    Q'.add_le_add_left (1 : Q') _ 0 (neg_nonpos_of_nonneg (Q'.pow_nonneg t ht0 K))
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (1 : Q'))))

/-- **`geomPartialSum_le` — the geometric partial-sum bound.**  For `0 ≤ t` and
`0 < 1 − t` (i.e. `t < 1`), every partial sum is bounded, K-uniformly, by
`1/(1 − t)`:

    Σ_{k<K} t^k  ≤  divPos 1 (1 − t)  =  1/(1 − t) .

From the telescope `(1 − t)·Σ ≃ 1 − t^K ≤ 1` and `le_divPos_of_mul_le`. -/
theorem geomPartialSum_le {t : Q'} (ht0 : (0 : Q') ≤ t)
    (hpos : (0 : Q') < (1 : Q') - t) (K : Nat) :
    tailSum (fun k => t ^ k) 0 K ≤ Q'.divPos 1 ((1 : Q') - t) hpos := by
  refine Q'.le_divPos_of_mul_le 1 ((1 : Q') - t) hpos ?_
  -- S·(1−t) ≃ (1−t)·S ≃ 1 − t^K ≤ 1
  have hcomm : (tailSum (fun k => t ^ k) 0 K * ((1 : Q') - t)).eqv
      (((1 : Q') - t) * tailSum (fun k => t ^ k) 0 K) :=
    Q'.mul_comm_eqv (tailSum (fun k => t ^ k) 0 K) ((1 : Q') - t)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hcomm (geomTelescope t K))) ?_
  exact oneSub_pow_le_one ht0 K

/-! ## 2. THE FLOW-CONTRACTION SUM `Σ_{k<K} a_k ≤ a_0/(1 − t)` -/

/-- **`contraction_pow` — geometric decay from a per-step contraction.**  If
`a_{k+1} ≤ t·a_k`, `0 ≤ a_k`, `0 ≤ t`, then `a_k ≤ a_0·t^k`. -/
theorem contraction_pow (a : Nat → Q') (t : Q') (ht0 : (0 : Q') ≤ t)
    (hcon : ∀ k, a (k + 1) ≤ t * a k) :
    ∀ k, a k ≤ a 0 * t ^ k := by
  intro k
  induction k with
  | zero =>
    show a 0 ≤ a 0 * t ^ 0
    exact Q'.ge_of_eqv (Q'.mul_one_eqv (a 0))
  | succ k ih =>
    show a (k + 1) ≤ a 0 * t ^ (k + 1)
    -- a(k+1) ≤ t·a_k ≤ t·(a_0·t^k) ≃ a_0·(t·t^k) = a_0·t^{k+1}
    have hmono : t * a k ≤ t * (a 0 * t ^ k) :=
      Q'.mul_le_mul_of_nonneg_left (a k) (a 0 * t ^ k) t ih ht0
    have hre : (t * (a 0 * t ^ k)).eqv (a 0 * (t * t ^ k)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv t (a 0) (t ^ k))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (t ^ k) (Q'.mul_comm_eqv t (a 0))) ?_
      exact Q'.mul_assoc_eqv (a 0) t (t ^ k)
    exact Q'.le_trans' _ _ _ (hcon k)
      (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hre))

/-- **`geom_budget_bound` — the K-independent contraction sum bound.**  Given a
nonnegative sequence with a per-step contraction `a_{k+1} ≤ t·a_k` (`0 ≤ t < 1`),

    Σ_{k<K} a_k  ≤  a_0 · 1/(1 − t) ,   K-uniformly. -/
theorem geom_budget_bound (a : Nat → Q') (t : Q') (ht0 : (0 : Q') ≤ t)
    (hpos : (0 : Q') < (1 : Q') - t) (ha0 : (0 : Q') ≤ a 0)
    (hcon : ∀ k, a (k + 1) ≤ t * a k) (K : Nat) :
    tailSum a 0 K ≤ a 0 * Q'.divPos 1 ((1 : Q') - t) hpos := by
  -- termwise: a_j ≤ a_0·t^j, then pull a_0 out and apply the geometric bound
  have h1 : tailSum a 0 K ≤ tailSum (fun j => a 0 * t ^ j) 0 K :=
    tailSum_le_of_termwise (contraction_pow a t ht0 hcon) 0 K
  have h2 : (tailSum (fun j => a 0 * t ^ j) 0 K).eqv
      (a 0 * tailSum (fun k => t ^ k) 0 K) :=
    tailSum_const_mul (a 0) (fun k => t ^ k) 0 K
  have h3 : a 0 * tailSum (fun k => t ^ k) 0 K
      ≤ a 0 * Q'.divPos 1 ((1 : Q') - t) hpos :=
    Q'.mul_le_mul_of_nonneg_left _ _ (a 0) (geomPartialSum_le ht0 hpos K) ha0
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2) h3)

/-! ## 3. THE SQUARED-MARGIN CONTRACTION AND THE `Σ m_k²` BUDGET -/

/-- **`sq_contraction` — the squared margins contract with rate `ρ²`.**  From the
margin contraction `m_{k+1} ≤ ρ·m_k` (`m ≥ 0`, `ρ ≥ 0`):

    m_{k+1}²  ≤  (ρ·ρ)·m_k² . -/
theorem sq_contraction (m : Nat → Q') (ρ : Q') (hρ0 : (0 : Q') ≤ ρ)
    (hmnn : ∀ k, (0 : Q') ≤ m k) (hcon : ∀ k, m (k + 1) ≤ ρ * m k) (k : Nat) :
    m (k + 1) * m (k + 1) ≤ (ρ * ρ) * (m k * m k) := by
  have hb : (0 : Q') ≤ ρ * m k := Q'.mul_nonneg _ _ hρ0 (hmnn k)
  -- m(k+1)·m(k+1) ≤ (ρ·m_k)·(ρ·m_k)
  have hsq : m (k + 1) * m (k + 1) ≤ (ρ * m k) * (ρ * m k) :=
    Q'.mul_le_mul_of_nonneg (hcon k) (hcon k) hb (hmnn (k + 1))
  exact Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv (sqProd_regroup ρ (m k)))

/-- **`crossover_sq_sum_le` — the K-independent squared-margin crossover sum.**
Given a margin flow contraction `m_{k+1} ≤ ρ·m_k` (`0 ≤ ρ`, `ρ² < 1`, `m ≥ 0`),

    Σ_{k<K} m_k²  ≤  m_0² · 1/(1 − ρ²) ,   K-uniformly. -/
theorem crossover_sq_sum_le (m : Nat → Q') (ρ : Q') (hρ0 : (0 : Q') ≤ ρ)
    (hpos : (0 : Q') < (1 : Q') - ρ * ρ)
    (hmnn : ∀ k, (0 : Q') ≤ m k) (hcon : ∀ k, m (k + 1) ≤ ρ * m k) (K : Nat) :
    tailSum (fun k => m k * m k) 0 K
      ≤ (m 0 * m 0) * Q'.divPos 1 ((1 : Q') - ρ * ρ) hpos := by
  have hnn0 : (0 : Q') ≤ (fun k => m k * m k) 0 := Q'.mul_nonneg _ _ (hmnn 0) (hmnn 0)
  exact geom_budget_bound (fun k => m k * m k) (ρ * ρ)
    (Q'.mul_nonneg _ _ hρ0 hρ0) hpos hnn0
    (sq_contraction m ρ hρ0 hmnn hcon) K

/-! ## 4. THE δ-BUDGET AND THE `CrossoverWindowDefect` PRODUCER -/

/-- **`crossover_sum_le` — the K-independent block-spin defect crossover budget.**
Given a per-step quadratic defect `δ_k ≤ sixp·m_k²` (`sixp = 6p ≥ 0`; the proved
`RenDefectQuadFactor.bondMovingDeltaRen_le_sixp` shape) and the margin flow
contraction `m_{k+1} ≤ ρ·m_k` (`ρ² < 1`),

    Σ_{k<K} δ_k  ≤  sixp · (m_0² · 1/(1 − ρ²))  =:  Bcrossδ ,   K-uniformly. -/
theorem crossover_sum_le (δ m : Nat → Q') (ρ sixp : Q')
    (hsixp : (0 : Q') ≤ sixp) (hρ0 : (0 : Q') ≤ ρ)
    (hpos : (0 : Q') < (1 : Q') - ρ * ρ)
    (hmnn : ∀ k, (0 : Q') ≤ m k) (hcon : ∀ k, m (k + 1) ≤ ρ * m k)
    (hδ : ∀ k, δ k ≤ sixp * (m k * m k)) (K : Nat) :
    tailSum δ 0 K
      ≤ sixp * ((m 0 * m 0) * Q'.divPos 1 ((1 : Q') - ρ * ρ) hpos) := by
  -- Σ δ ≤ Σ sixp·m² ≃ sixp·Σ m² ≤ sixp·(m_0²·1/(1−ρ²))
  have h1 : tailSum δ 0 K ≤ tailSum (fun k => sixp * (m k * m k)) 0 K :=
    tailSum_le_of_termwise hδ 0 K
  have h2 : (tailSum (fun k => sixp * (m k * m k)) 0 K).eqv
      (sixp * tailSum (fun k => m k * m k) 0 K) :=
    tailSum_const_mul sixp (fun k => m k * m k) 0 K
  have h3 : sixp * tailSum (fun k => m k * m k) 0 K
      ≤ sixp * ((m 0 * m 0) * Q'.divPos 1 ((1 : Q') - ρ * ρ) hpos) :=
    Q'.mul_le_mul_of_nonneg_left _ _ sixp
      (crossover_sq_sum_le m ρ hρ0 hpos hmnn hcon K) hsixp
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv h2) h3)

/-- **`crossoverDefect_ofFlowContraction` — the crossover obligation from ONE
flow-contraction fact.**  A geometric margin flow contraction `m_{k+1} ≤ ρ·m_k`
(`ρ² < 1`) with the quadratic defect `δ_k ≤ sixp·m_k²` and a per-step additive cap
`ε_j ≤ εmax` (`j < K`) inhabits the single named crossover obligation
`CrossoverWindowDefect δ ε K` with the K-INDEPENDENT multiplicative budget

    Bδ  =  sixp · (m_0² · 1/(1 − ρ²))

(and `Bε = K·εmax`).  This CONSUMES the flow-contraction hypothesis (a genuine RG
input — the true AF harmonic flow does not have a uniform `ρ < 1` in the deep UV);
nothing is inhabited unconditionally, so the frontier obligation stays open. -/
def crossoverDefect_ofFlowContraction (δ ε m : Nat → Q') (K : Nat)
    (ρ sixp εmax : Q')
    (hsixp : (0 : Q') ≤ sixp) (hρ0 : (0 : Q') ≤ ρ)
    (hpos : (0 : Q') < (1 : Q') - ρ * ρ) (hεmax : (0 : Q') ≤ εmax)
    (hmnn : ∀ k, (0 : Q') ≤ m k) (hcon : ∀ k, m (k + 1) ≤ ρ * m k)
    (hδ : ∀ k, δ k ≤ sixp * (m k * m k))
    (hstepε : ∀ j, j < K → ε j ≤ εmax) :
    CrossoverWindowDefect δ ε K where
  Bδ := sixp * ((m 0 * m 0) * Q'.divPos 1 ((1 : Q') - ρ * ρ) hpos)
  Bε := Q'.ofNat K * εmax
  crossδ := crossover_sum_le δ m ρ sixp hsixp hρ0 hpos hmnn hcon hδ K
  crossε := tailSum_le_ofNat_mul ε εmax hεmax K hstepε

/-! ## 5. THE WHOLE FLOOR FROM ONE FLOW-CONTRACTION FACT (unification with the
     `DefectGapRecursion` survival-product route)

Feeding `crossoverDefect_ofFlowContraction` into
`CrossoverAnchorFloor.fullFloor_reduced_to_crossover` gives the entire positive
continuum floor from a SINGLE geometric flow-contraction fact `ρ² < 1`, with the
anchor the PROVED strong-coupling gap and the deep-UV tail AF-derived.  This is the
same summable-defect content as `DominantModeRecursion.dominantModeRecursion`'s
`prodFloor` (a summable `δ_k ≤ 6p(1 − w_k)²` ⇒ positive survival-product floor):
the crossover budget sum and the survival-product floor are two views of the same
geometric-summability fact. -/

/-- **`fullFloor_of_flowContraction` — the entire continuum floor on ONE geometric
flow-contraction fact.**  With the margin flow contraction `m_{k+1} ≤ ρ·m_k`
(`ρ² < 1`), the quadratic defect `δ_k ≤ sixp·m_k²`, a per-step additive cap, the
PROVED strong-coupling anchor (`hanchor0`), the AF deep-UV tail (`hUVδ`/`hUVε`), and
the anchor-dominance, the margin has a strictly positive uniform floor.  Everything
is proved EXCEPT the flow contraction `hcon` (the ONE genuine crossover input). -/
theorem fullFloor_of_flowContraction
    (margin δ ε m : Nat → Q') (K : Nat) (Dδ Dε ρ sixp εmax : Q')
    (hsixp : (0 : Q') ≤ sixp) (hρ0 : (0 : Q') ≤ ρ)
    (hpos : (0 : Q') < (1 : Q') - ρ * ρ) (hεmax : (0 : Q') ≤ εmax)
    (hmnn : ∀ k, (0 : Q') ≤ m k) (hcon : ∀ k, m (k + 1) ≤ ρ * m k)
    (hδbound : ∀ k, δ k ≤ sixp * (m k * m k))
    (hstepε : ∀ j, j < K → ε j ≤ εmax)
    (hstep : ∀ k, (1 - δ k) * margin k - ε k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k)
    (hanchor0 : margin 0 = strongAnchor)
    (hDδ : (0 : Q') ≤ Dδ) (hDε : (0 : Q') ≤ Dε)
    (hUVδ : ∀ k, K ≤ k → δ k ≤ Dδ * recipSqSucc k)
    (hUVε : ∀ k, K ≤ k → ε k ≤ Dε * recipSqSucc k)
    (hanchor :
      (crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0 hpos hεmax
        hmnn hcon hδbound hstepε).Bε + 2 * Dε
        < (1 - ((crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0
              hpos hεmax hmnn hcon hδbound hstepε).Bδ + 2 * Dδ)) * margin 0) :
    ∀ k,
      (1 - ((crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0 hpos
          hεmax hmnn hcon hδbound hstepε).Bδ + 2 * Dδ)) * margin 0
        - ((crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0 hpos
            hεmax hmnn hcon hδbound hstepε).Bε + 2 * Dε) ≤ margin k
      ∧ (0 : Q') <
        (1 - ((crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0 hpos
            hεmax hmnn hcon hδbound hstepε).Bδ + 2 * Dδ)) * margin 0
        - ((crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0 hpos
            hεmax hmnn hcon hδbound hstepε).Bε + 2 * Dε) :=
  fullFloor_reduced_to_crossover margin δ ε K Dδ Dε
    (crossoverDefect_ofFlowContraction δ ε m K ρ sixp εmax hsixp hρ0 hpos hεmax
      hmnn hcon hδbound hstepε)
    hstep hδnn hδ1 hεnn hanchor0 hDδ hDε hUVδ hUVε hanchor

/-! ## 6. COMPLEMENTARITY — the block-spin defect controls the character-fail window

The character mechanism has rate `ρ_char = 2w³`, `< 1` only for `w < 2^{−1/3}`
(`w³ < 1/2`).  The block-spin per-step defect `6p(1 − w)²` is SMALL near `w = 1`.
At the concrete handoff `w* = 79/100` BOTH hold; and the block-spin per-step defect
stays `< 1/2` on the whole tail `[w*, 1]`. -/

/-- The concrete handoff weight `w* = 79/100` — strictly below the character ceiling
`2^{−1/3} ≈ 0.7937`, and above the block-spin threshold `≈ 0.711`. -/
def wStar : Q' := Q'.mkPos 79 100 (by decide)

/-- The handoff margin `m* = 1 − w* = 21/100`. -/
def mStar : Q' := Q'.mkPos 21 100 (by decide)

/-- `m* = 1 − w*` (definitional check). -/
theorem mStar_eq : mStar = (1 : Q') - wStar := by decide

/-- **The handoff is below the character ceiling:** `w*³ < 1/2` (so the character
rate `ρ_char = 2w*³ < 1` — the character mechanism is still valid at `w*`). -/
theorem wStar_below_ceiling : wStar ^ 3 < Q'.mkPos 1 2 (by decide) := by decide

/-- **The character rate is `< 1` at the handoff:** `2·w*³ < 1`. -/
theorem char_rate_lt_one_at_handoff :
    Q'.ofNat 2 * wStar ^ 3 < (1 : Q') := by decide

/-- **The block-spin per-step defect is `< 1/2` at the handoff** (`p = 1`):
`6·m*² = 6·(21/100)² = 2646/10000 < 1/2`.  So at `w*` BOTH mechanisms are valid —
a clean handoff with NO coverage gap. -/
theorem blockspin_perstep_at_handoff :
    Q'.ofNat 6 * (mStar * mStar) < Q'.mkPos 1 2 (by decide) := by decide

/-- **`blockspin_perstep_le_handoff` — the block-spin per-step defect stays `< 1/2`
on the WHOLE tail `[w*, 1]` (UNCONDITIONAL).**  For `w* ≤ w ≤ 1`,

    6·(1 − w)²  ≤  6·m*²  <  1/2 ,

because `1 − w ≤ m*` and squaring is monotone on the nonnegatives.  This is the
region `(2^{−1/3}, 1]` where the character mechanism FAILS: the block-spin defect
controls it, at the per-step level, with the OPPOSITE scaling to characters. -/
theorem blockspin_perstep_le_handoff {w : Q'} (hlo : wStar ≤ w) (hhi : w ≤ (1 : Q')) :
    Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) < Q'.mkPos 1 2 (by decide) := by
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hhi
  -- 1 − w ≤ 1 − w* = m*  (subtraction is antitone in the subtrahend)
  have hle : (1 : Q') - w ≤ mStar := by
    rw [mStar_eq]
    -- 1 + (−w) ≤ 1 + (−w*), from −w ≤ −w*
    exact Q'.add_le_add_left (1 : Q') (-w) (-wStar) (Q'.neg_le_neg hlo)
  -- 6·(1−w)² ≤ 6·m*² < 1/2
  have hsq : ((1 : Q') - w) * ((1 : Q') - w) ≤ mStar * mStar :=
    BondMovingQuadratic.sq_le_sq hnn hle
  have h6 : Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w))
      ≤ Q'.ofNat 6 * (mStar * mStar) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 6) hsq (by decide)
  exact Q'.lt_of_le_of_lt h6 blockspin_perstep_at_handoff

/-! ## 7. THE NUMERIC BUDGET CHECK — a concrete PASSING instance `Bcrossδ + 2Dδ < 1/2`

Instantiate the assembled crossover budget at:
  * `p = 1`      ⟹ `sixp = 6`;
  * handoff `m_0 = m* = 21/100`  (block-spin starts at `w* = 79/100`);
  * flow contraction `ρ² = 1/4`  ⟹ `1/(1 − ρ²) = 1/(3/4) = 4/3`;
  * AF deep-UV scale `Dδ = 1/100`.

Then
    Bcrossδ = 6 · (21/100)² · 4/3 = 3528/10000 = 0.3528 ,
    Bcrossδ + 2·Dδ = 0.3528 + 0.02 = 0.3728 < 1/2 .

Both facts are decidable `Q'` rationals.  With the anchor `margin 0 = 107/108` and no
additive erosion this clears the anchor-dominance and leaves a floor
`(1 − 0.3728)·(107/108) > 0`. -/

/-- The assembled budget `Bcrossδ = 6·(21/100)²·(4/3)` equals the rational
`3528/10000` (`decide`-checked); here `4/3 = 1/(1 − ρ²)` at `ρ² = 1/4`. -/
theorem assembled_Bcross_value :
    (Q'.ofNat 6 * ((mStar * mStar) * Q'.mkPos 4 3 (by decide))).eqv
      (Q'.mkPos 3528 10000 (by decide)) := by decide

/-- **`numeric_budget_clears` — the concrete total budget clears `< 1/2`.**
`Bcrossδ + 2·Dδ = 6·(21/100)²·(4/3) + 2·(1/100) = 3728/10000 < 1/2`.  A PASSING
instance of the anchor-dominance target with `m_0 = m*`, `ρ² = 1/4`, `Dδ = 1/100`,
`p = 1`. -/
theorem numeric_budget_clears :
    Q'.ofNat 6 * ((mStar * mStar) * Q'.mkPos 4 3 (by decide))
        + Q'.ofNat 2 * Q'.mkPos 1 100 (by decide)
      < Q'.mkPos 1 2 (by decide) := by decide

/-- The block-spin handoff `w* = 79/100` genuinely lies in the OVERLAP of the two
mechanisms: below the character ceiling (`w*³ = 493039/1000000 < 1/2`) AND above the
block-spin threshold (`6·m*² < 1/2`).  So the character window `[0, w*]` and the
block-spin window `[w*, 1]` COVER `[0, 1]` with a clean handoff — no gap. -/
theorem handoff_in_overlap :
    (wStar ^ 3 < Q'.mkPos 1 2 (by decide))
      ∧ (Q'.ofNat 6 * (mStar * mStar) < Q'.mkPos 1 2 (by decide)) :=
  ⟨wStar_below_ceiling, blockspin_perstep_at_handoff⟩

end YMGap.Continuum.CrossoverFlowContraction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CrossoverFlowContraction.sqProd_regroup
#print axioms YMGap.Continuum.CrossoverFlowContraction.geomTelescope
#print axioms YMGap.Continuum.CrossoverFlowContraction.geomPartialSum_le
#print axioms YMGap.Continuum.CrossoverFlowContraction.contraction_pow
#print axioms YMGap.Continuum.CrossoverFlowContraction.geom_budget_bound
#print axioms YMGap.Continuum.CrossoverFlowContraction.sq_contraction
#print axioms YMGap.Continuum.CrossoverFlowContraction.crossover_sq_sum_le
#print axioms YMGap.Continuum.CrossoverFlowContraction.crossover_sum_le
#print axioms YMGap.Continuum.CrossoverFlowContraction.crossoverDefect_ofFlowContraction
#print axioms YMGap.Continuum.CrossoverFlowContraction.fullFloor_of_flowContraction
#print axioms YMGap.Continuum.CrossoverFlowContraction.blockspin_perstep_le_handoff
#print axioms YMGap.Continuum.CrossoverFlowContraction.assembled_Bcross_value
#print axioms YMGap.Continuum.CrossoverFlowContraction.numeric_budget_clears
#print axioms YMGap.Continuum.CrossoverFlowContraction.handoff_in_overlap
