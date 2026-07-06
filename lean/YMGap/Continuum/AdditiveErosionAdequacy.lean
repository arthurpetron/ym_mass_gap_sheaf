/-
Track B / R2 — **ADEQUACY of the additive-erosion floor**: deriving the positive
continuum limit of the true dimensionless margin from ELEMENTARY inputs, rather
than carrying it as data.

# What this module proves — and why it sharpens the honest residual

`TrueMarginRecursionPhysical` (`TrueMarginRecursionPhysical.lean`) carries its
positive continuum limit as Type-level DATA (`floorWitness`, `floorWitness_pos`,
`floorWitness_le`, `lowerBound`) — "the anchor-dominates-budget conclusion the
additive law cannot derive from summability alone".

This module DERIVES that conclusion.  The elementary telescoping analysis of the
additive-erosion recursion

    margin (k+1)  ≥  (1 − δ_k) · margin k  −  ε_k ,      δ_k ∈ [0,1], ε_k ≥ 0

with FINITE budget bounds `Σ_{j<k} δ_j ≤ B_δ` and `Σ_{j<k} ε_j ≤ B_ε`, yields the
uniform floor

    margin k  ≥  (1 − B_δ) · margin 0  −  B_ε  =:  floorWitness           (∀ k)

and, under the genuine **anchor-dominates-budget** hypothesis
`B_ε < (1 − B_δ) · margin 0`, `floorWitness > 0`.

The proof folds the Weierstrass product bound `∏(1−δ_j) ≥ 1 − Σδ_j` and the
`Q_{j,k} ≤ 1` erosion-weight bound directly into a SINGLE inductive invariant

    margin k  ≥  (1 − Σ_{j<k} δ_j) · margin 0  −  Σ_{j<k} ε_j ,

which is closed under the step law using only `0 ≤ δ_k`, `δ_k ≤ 1`, `ε_k ≥ 0`,
`0 ≤ margin 0` — no infinite products, no analysis.  The whole "positive limit"
narrative is thereby reduced to the ONE elementary rational inequality
`(1 − Σδ) · m₀ > Σε` on the block-spin defects.

# What is stated / proved here (axiom-clean; Rule 8 Type-level data)

  * `additiveErosion_uniform_floor` — THE ADEQUACY (pure `Q'`): the telescoping
    lower bound + anchor-dominance ⟹ `∀ k, floorWitness ≤ margin k ∧ 0 < floorWitness`.

  * `TrueMarginRecursionSummable` — the SHARPER carrier (a `Type`, DELIBERATELY
    UNINHABITED): the same physical `step`/`budget_modulus` as the physical carrier,
    PLUS the explicit finite budget split (`Bδ`, `Bε`) and the anchor-dominance
    inequality `anchorDominates`.  It does NOT carry `Δ`/`floorWitness_pos`/
    `lowerBound` — those are DERIVED.

  * `TrueMarginRecursionSummable.toPhysical` — constructs a
    `TrueMarginRecursionPhysical` whose positivity witnesses are PROVED (via the
    adequacy), not asserted.  A `TrueMarginRecursionSummable` therefore feeds the
    whole φ⁴→YM bridge with its positive continuum limit derived.

The analytic discharge (inhabiting `step` + `budget` + `anchorDominates` for the
non-abelian multi-link 4D block-spin margin) is out of scope; the structure is NOT
inhabited here.  The open content is now the single elementary block-spin
inequality `(1 − Σδ) · m₀ > Σε`.
-/
import YMGap.Continuum.TrueMarginRecursionPhysical
import YMGap.Constructive.QPoly

namespace YMGap.Continuum

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SummableInverseSquare

/-! ## 1. Small `Q'` order/sign helpers (pure `Int` cross-products / `eqv` glue) -/

/-- `0 ≤ a → -a ≤ 0`. -/
theorem qNegNonpos {a : Q'} (h : (0 : Q') ≤ a) : -a ≤ (0 : Q') := by
  have ha : (0 : Int) ≤ a.num := (Q'.zero_le_iff_num_nonneg a).mp h
  show (-(a.num)) * (1 : Int) ≤ (0 : Int) * ((-a).den : Int)
  rw [Int.mul_one, Int.zero_mul]
  omega

/-- `a ≤ b → 0 ≤ b + -a`. -/
theorem qZeroLeSub {a b : Q'} (h : a ≤ b) : (0 : Q') ≤ b + -a := by
  have h1 : a + -a ≤ b + -a := Q'.add_le_add_right a b (-a) h
  have h0 : (0 : Q').eqv (a + -a) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv a (-a)) (Q'.neg_add_self_eqv a))
  exact Q'.le_trans' 0 (a + -a) (b + -a) (Q'.le_of_eqv h0) h1

/-- `a ≤ b → -b ≤ -a`. -/
theorem qNegLeNeg {a b : Q'} (h : a ≤ b) : -b ≤ -a := by
  have h' : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := h
  show (-(b.num)) * (a.den : Int) ≤ (-(a.num)) * (b.den : Int)
  rw [Int.neg_mul, Int.neg_mul]
  exact Int.neg_le_neg h'

/-- `c < d → 0 < d + -c`. -/
theorem qSubPosOfLt {c d : Q'} (h : c < d) : (0 : Q') < d + -c := by
  have hlt : c.num * (d.den : Int) < d.num * (c.den : Int) := h
  show (0 : Int) * ((d + -c).den : Int) < (d + -c).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  have hnum : (d + -c).num = d.num * (c.den : Int) + (-(c.num)) * (d.den : Int) := rfl
  rw [hnum, Int.neg_mul]
  omega

/-- Right-distributivity of subtraction (local copy): `(a + -b)·c ≃ a·c + -(b·c)`. -/
theorem qSubMulEqv (a b c : Q') : ((a + -b) * c).eqv (a * c + -(b * c)) :=
  Q'.eqv_trans _ _ _ (Q'.add_mul_eqv a (-b) c)
    (Q'.add_eqv_congr_left (a * c) ((-b) * c) (-(b * c)) (Q'.neg_mul_eqv b c))

/-! ## 2. The one-step telescoping inequality (the Weierstrass merge)

The single algebraic engine: from the accumulated lower bound `P = (1−s)·m − e`
(with `s = Σ_{j<k}δ`, `e = Σ_{j<k}ε`, `m = margin 0`) the stepped bound at `k+1`,
`(1−(s+δ))·m − (e+ε)`, is dominated by the recursion applied to `P`,
`(1−δ)·P − ε`.  The slack is exactly `δ·(m − P) ≥ 0` (the folded Weierstrass +
`Q ≤ 1` correction).  Pure `Q'`; `P` is kept atomic so no product exceeds degree
achievable by the `eqv`-congruence toolkit. -/

theorem additive_step_bound
    (s d e x m : Q')
    (hs : (0 : Q') ≤ s) (hd : (0 : Q') ≤ d) (he : (0 : Q') ≤ e)
    (hm : (0 : Q') ≤ m) :
    (1 - (s + d)) * m - (e + x)
      ≤ (1 - d) * ((1 - s) * m - e) - x := by
  -- (1) `(1−s)·m − e ≤ m`.
  have h1s1 : (1 : Q') - s ≤ 1 := by
    have hns : -s ≤ (0 : Q') := qNegNonpos hs
    have haux := Q'.add_le_add_left (1 : Q') (-s) 0 hns
    rw [Q'.add_zero'] at haux
    exact haux
  have hi : (1 - s) * m ≤ m := by
    have h2 : (1 - s) * m ≤ (1 : Q') * m :=
      Q'.mul_le_mul_of_nonneg_right (1 - s) 1 m h1s1 hm
    exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.one_mul_eqv m))
  have hPm : (1 - s) * m - e ≤ m := by
    show (1 - s) * m + -e ≤ m
    have hii : -e ≤ (0 : Q') := qNegNonpos he
    have c1 : (1 - s) * m + -e ≤ m + -e := Q'.add_le_add_right _ _ (-e) hi
    have c2 : m + -e ≤ m + (0 : Q') := Q'.add_le_add_left m (-e) 0 hii
    have c3 : m + (0 : Q') = m := Q'.add_zero' m
    rw [c3] at c2
    exact Q'.le_trans' _ _ _ c1 c2
  -- (2) `d·P ≤ d·m`, hence `-(d·m) ≤ -(d·P)`.
  have hdPdm : d * ((1 - s) * m - e) ≤ d * m :=
    Q'.mul_le_mul_of_nonneg_left ((1 - s) * m - e) m d hPm hd
  have hneg : -(d * m) ≤ -(d * ((1 - s) * m - e)) := qNegLeNeg hdPdm
  -- (3) Weierstrass expansion: `(1−(s+d))·m ≃ (1−s)·m + -(d·m)`.
  have hW : ((1 - (s + d)) * m).eqv ((1 - s) * m + -(d * m)) := by
    have e1 : ((1 - (s + d)) * m).eqv ((1 : Q') * m + -((s + d) * m)) :=
      qSubMulEqv 1 (s + d) m
    have e2 : (-((s + d) * m)).eqv (-(s * m) + -(d * m)) :=
      Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr ((s + d) * m) (s * m + d * m) (Q'.add_mul_eqv s d m))
        (Q'.neg_add_eqv (s * m) (d * m))
    have e3 : ((1 : Q') * m + -((s + d) * m)).eqv (m + (-(s * m) + -(d * m))) :=
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((1 : Q') * m) m (-((s + d) * m)) (Q'.one_mul_eqv m))
        (Q'.add_eqv_congr_left m (-((s + d) * m)) (-(s * m) + -(d * m)) e2)
    have e4 : (((1 - s) * m) + -(d * m)).eqv ((m + -(s * m)) + -(d * m)) :=
      Q'.add_eqv_congr_right ((1 - s) * m) (m + -(s * m)) (-(d * m))
        (Q'.eqv_trans _ _ _ (qSubMulEqv 1 s m)
          (Q'.add_eqv_congr_right ((1 : Q') * m) m (-(s * m)) (Q'.one_mul_eqv m)))
    have e5 : (m + (-(s * m) + -(d * m))).eqv ((m + -(s * m)) + -(d * m)) :=
      Q'.eqv_symm (Q'.add_assoc_eqv m (-(s * m)) (-(d * m)))
    exact Q'.eqv_trans _ _ _ e1
      (Q'.eqv_trans _ _ _ e3
        (Q'.eqv_trans _ _ _ e5 (Q'.eqv_symm e4)))
  -- (4) Piece A: `(1−(s+d))·m ≤ (1−s)·m + -(d·P)`.
  have pieceA : (1 - (s + d)) * m ≤ (1 - s) * m + -(d * ((1 - s) * m - e)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hW)
      (Q'.add_le_add_left ((1 - s) * m) (-(d * m)) (-(d * ((1 - s) * m - e))) hneg)
  -- (5) Piece B: `-(e+x) ≤ -e + -x` (an equivalence).
  have pieceB : -(e + x) ≤ -e + -x := Q'.le_of_eqv (Q'.neg_add_eqv e x)
  -- (6) Combine into a bound on the LHS.
  have comb : (1 - (s + d)) * m + -(e + x)
      ≤ ((1 - s) * m + -(d * ((1 - s) * m - e))) + (-e + -x) := by
    have t1 : (1 - (s + d)) * m + -(e + x)
        ≤ ((1 - s) * m + -(d * ((1 - s) * m - e))) + -(e + x) :=
      Q'.add_le_add_right _ _ (-(e + x)) pieceA
    have t2 : ((1 - s) * m + -(d * ((1 - s) * m - e))) + -(e + x)
        ≤ ((1 - s) * m + -(d * ((1 - s) * m - e))) + (-e + -x) :=
      Q'.add_le_add_left _ _ _ pieceB
    exact Q'.le_trans' _ _ _ t1 t2
  -- (7) Rearrange the intermediate to `((1−s)·m − e) + (-(d·P) + -x)`.
  have hinter :
      (((1 - s) * m + -(d * ((1 - s) * m - e))) + (-e + -x)).eqv
        (((1 - s) * m + -e) + (-(d * ((1 - s) * m - e)) + -x)) :=
    YMGap.Constructive.QPoly.q_interchange ((1 - s) * m)
      (-(d * ((1 - s) * m - e))) (-e) (-x)
  -- (8) `(1−d)·P ≃ P + -(d·P)`.
  have hR1 : ((1 - d) * ((1 - s) * m - e)).eqv
      (((1 - s) * m - e) + -(d * ((1 - s) * m - e))) := by
    have hbase := qSubMulEqv 1 d ((1 - s) * m - e)
    exact Q'.eqv_trans _ _ _ hbase
      (Q'.add_eqv_congr_right ((1 : Q') * ((1 - s) * m - e)) ((1 - s) * m - e)
        (-(d * ((1 - s) * m - e))) (Q'.one_mul_eqv ((1 - s) * m - e)))
  have hRHS : ((1 - d) * ((1 - s) * m - e) + -x).eqv
      ((((1 - s) * m - e) + -(d * ((1 - s) * m - e))) + -x) :=
    Q'.add_eqv_congr_right _ _ (-x) hR1
  have hTassoc :
      (((1 - s) * m - e) + (-(d * ((1 - s) * m - e)) + -x)).eqv
        ((((1 - s) * m - e) + -(d * ((1 - s) * m - e))) + -x) :=
    Q'.eqv_symm
      (Q'.add_assoc_eqv ((1 - s) * m - e) (-(d * ((1 - s) * m - e))) (-x))
  -- (9) The intermediate is `eqv` the recursion RHS.
  have hfinal :
      (((1 - s) * m + -(d * ((1 - s) * m - e))) + (-e + -x)).eqv
        ((1 - d) * ((1 - s) * m - e) + -x) :=
    Q'.eqv_trans _ _ _ hinter
      (Q'.eqv_trans _ _ _ hTassoc (Q'.eqv_symm hRHS))
  exact Q'.le_trans' _ _ _ comb (Q'.le_of_eqv hfinal)

/-! ## 3. THE ADEQUACY LEMMA — positive uniform floor from elementary inputs -/

/-- **ADEQUACY (pure `Q'`).**  Given the additive-erosion step law, `δ_k ∈ [0,1]`,
`ε_k ≥ 0`, `0 ≤ margin 0`, the FINITE budget bounds `Σ_{j<k}δ_j ≤ B_δ` and
`Σ_{j<k}ε_j ≤ B_ε`, and the **anchor-dominates-budget** inequality
`B_ε < (1 − B_δ)·margin 0`, the margin is uniformly bounded below by the strictly
positive floor `floorWitness = (1 − B_δ)·margin 0 − B_ε`:

    ∀ k, floorWitness ≤ margin k  ∧  0 < floorWitness.

The positive continuum limit is thus DERIVED, not asserted. -/
theorem additiveErosion_uniform_floor
    (margin δ ε : Nat → Q') (Bδ Bε : Q')
    (hstep : ∀ k, (1 - δ k) * margin k - ε k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hεnn : ∀ k, (0 : Q') ≤ ε k)
    (hm0 : (0 : Q') ≤ margin 0)
    (hBδ : ∀ k, tailSum δ 0 k ≤ Bδ)
    (hBε : ∀ k, tailSum ε 0 k ≤ Bε)
    (hanchor : Bε < (1 - Bδ) * margin 0) :
    ∀ k, (1 - Bδ) * margin 0 - Bε ≤ margin k
       ∧ (0 : Q') < (1 - Bδ) * margin 0 - Bε := by
  -- floorWitness > 0 from anchor-dominance.
  have hpos : (0 : Q') < (1 - Bδ) * margin 0 - Bε := qSubPosOfLt hanchor
  -- The folded telescoping invariant.
  have INV : ∀ k,
      (1 - tailSum δ 0 k) * margin 0 - tailSum ε 0 k ≤ margin k := by
    intro k
    induction k with
    | zero =>
      show ((1 : Q') - 0) * margin 0 - 0 ≤ margin 0
      rw [Q'.sub_zero', Q'.sub_zero']
      exact Q'.le_of_eqv (Q'.one_mul_eqv (margin 0))
    | succ k ih =>
      have hSd : tailSum δ 0 (k + 1) = tailSum δ 0 k + δ k := by
        show tailSum δ 0 k + δ (0 + k) = tailSum δ 0 k + δ k
        rw [Nat.zero_add]
      have hSe : tailSum ε 0 (k + 1) = tailSum ε 0 k + ε k := by
        show tailSum ε 0 k + ε (0 + k) = tailSum ε 0 k + ε k
        rw [Nat.zero_add]
      rw [hSd, hSe]
      have hs := tailSum_nonneg δ hδnn 0 k
      have he := tailSum_nonneg ε hεnn 0 k
      have step1 :
          (1 - (tailSum δ 0 k + δ k)) * margin 0 - (tailSum ε 0 k + ε k)
            ≤ (1 - δ k) * ((1 - tailSum δ 0 k) * margin 0 - tailSum ε 0 k) - ε k :=
        additive_step_bound (tailSum δ 0 k) (δ k) (tailSum ε 0 k) (ε k) (margin 0)
          hs (hδnn k) he hm0
      have h1md : (0 : Q') ≤ 1 - δ k := qZeroLeSub (hδ1 k)
      have step2 :
          (1 - δ k) * ((1 - tailSum δ 0 k) * margin 0 - tailSum ε 0 k) - ε k
            ≤ (1 - δ k) * margin k - ε k :=
        Q'.add_le_add_right _ _ (-(ε k))
          (Q'.mul_le_mul_of_nonneg_left _ _ (1 - δ k) ih h1md)
      exact Q'.le_trans' _ _ _ step1 (Q'.le_trans' _ _ _ step2 (hstep k))
  intro k
  refine ⟨?_, hpos⟩
  -- floorWitness ≤ (folded bound at k) ≤ margin k.
  have hA : (1 - Bδ) * margin 0 ≤ (1 - tailSum δ 0 k) * margin 0 := by
    have hcoef : (1 : Q') - Bδ ≤ 1 - tailSum δ 0 k :=
      Q'.add_le_add_left 1 (-Bδ) (-(tailSum δ 0 k)) (qNegLeNeg (hBδ k))
    exact Q'.mul_le_mul_of_nonneg_right (1 - Bδ) (1 - tailSum δ 0 k) (margin 0) hcoef hm0
  have hB : -Bε ≤ -(tailSum ε 0 k) := qNegLeNeg (hBε k)
  have c1 : (1 - Bδ) * margin 0 + -Bε ≤ (1 - tailSum δ 0 k) * margin 0 + -Bε :=
    Q'.add_le_add_right _ _ (-Bε) hA
  have c2 : (1 - tailSum δ 0 k) * margin 0 + -Bε
      ≤ (1 - tailSum δ 0 k) * margin 0 + -(tailSum ε 0 k) :=
    Q'.add_le_add_left _ _ _ hB
  exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ c1 c2) (INV k)

/-! ## 4. The sharper carrier — anchor-dominance as ELEMENTARY data

`TrueMarginRecursionSummable` carries the same physical objects as
`TrueMarginRecursionPhysical` (`margin_def` via `Q'.divPos`, the ADDITIVE `step`,
the `GradedTowerSummable`-shaped `budget_modulus`) PLUS the explicit finite budget
split `(Bδ, Bε)` and the anchor-dominance inequality — but does NOT carry the
positive-limit witnesses `floorWitness_pos`/`lowerBound`.  Those are DERIVED by
`toPhysical`.  DELIBERATELY UNINHABITED here: the analytic `step`/`budget`/
`anchorDominates` for the non-abelian 4D block-spin margin is the open Clay core. -/

/-- **THE ADDITIVE-EROSION RECURSION WITH ELEMENTARY ANCHOR-DOMINANCE (`Type`).**
Everything the physical carrier needs, with the positive continuum limit no longer
carried as data — it is reconstructed by `toPhysical` from the single elementary
inequality `anchorDominates : Bε < (1 − Bδ)·margin 0`.  UNINHABITED here. -/
structure TrueMarginRecursionSummable : Type where
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
  /-- The anchor margin `margin 0` is nonnegative (mass/spacing ratio). -/
  margin0_nonneg : (0 : Q') ≤ margin 0
  /-- The tail-modulus constant for the `(δ+ε)` budget. -/
  budgetTailConst : Q'
  /-- **Rule-8.3 explicit tail-rate witness** (mirrors `GradedTowerSummable`). -/
  budget_modulus : ∀ N M,
      tailSum (fun k => δ k + ε k) N M ≤ budgetTailConst * pot 2 (by decide) N
  /-- Finite budget bound on the defect partial sums. -/
  Bδ : Q'
  /-- Finite budget bound on the erosion partial sums. -/
  Bε : Q'
  /-- `Σ_{j<k} δ_j ≤ Bδ` at every scale. -/
  budgetSplit_δ : ∀ k, tailSum δ 0 k ≤ Bδ
  /-- `Σ_{j<k} ε_j ≤ Bε` at every scale. -/
  budgetSplit_ε : ∀ k, tailSum ε 0 k ≤ Bε
  /-- **THE ANCHOR-DOMINATES-BUDGET INEQUALITY** — the genuine physics condition
  `(1 − Σδ)·m₀ > Σε`, strictly more elementary than asserting `Δ > 0`. -/
  anchorDominates : Bε < (1 - Bδ) * margin 0

/-- **ADEQUACY BRIDGE.**  A `TrueMarginRecursionSummable` yields a
`TrueMarginRecursionPhysical` whose positive continuum limit is PROVED (via
`additiveErosion_uniform_floor`), not asserted.  `Δ` and its floor witnesses are
constructed from the elementary anchor-dominance data. -/
def TrueMarginRecursionSummable.toPhysical
    (T : TrueMarginRecursionSummable) : TrueMarginRecursionPhysical where
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
  budgetTailConst := T.budgetTailConst
  budget_modulus := T.budget_modulus
  Δ := CReal.ofQ' ((1 - T.Bδ) * T.margin 0 - T.Bε)
  floorWitness := (1 - T.Bδ) * T.margin 0 - T.Bε
  floorWitness_pos :=
    (additiveErosion_uniform_floor T.margin T.δ T.ε T.Bδ T.Bε T.step
      T.δ_nonneg T.δ_le_one T.ε_nonneg T.margin0_nonneg
      T.budgetSplit_δ T.budgetSplit_ε T.anchorDominates 0).2
  floorWitness_le := CReal.le_refl _
  lowerBound := fun k =>
    CReal.leEv_of_le (CReal.ofQ'_le_ofQ'
      (additiveErosion_uniform_floor T.margin T.δ T.ε T.Bδ T.Bε T.step
        T.δ_nonneg T.δ_le_one T.ε_nonneg T.margin0_nonneg
        T.budgetSplit_δ T.budgetSplit_ε T.anchorDominates k).1)

end YMGap.Continuum

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.additive_step_bound
#print axioms YMGap.Continuum.additiveErosion_uniform_floor
#print axioms YMGap.Continuum.TrueMarginRecursionSummable.toPhysical
