/-
Piece C of the uniform SU(2) heat-kernel PSD program — the **algebraic
reduction** turning Gram positive-semidefiniteness into functional positivity,
uniformly in `N`.

This is the clean bridge that makes Pieces A+B (heat-kernel character
positivity + integration) imply the uniform PSD of the character Gram matrix at
*every* order `N` simultaneously.  It is pure algebra: the Gram quadratic form
IS the moment functional applied to a square, and PSD ⟸ functional-positivity is
the quadratic-form expansion.

# The picture

For the SU(2) character moments `m_s = ⟨χ_{s/2}⟩` (`= (s+1)·a^{s(s+2)}`,
the heat-kernel `wilsonCharExp`) the **Gram matrix** of the character basis is

    G_{ij} = ⟨χ_i χ_j⟩ = Σ_{c = |i−j|, step 2}^{i+j} m_c,

each entry a finite sum of moments via the SU(2) Clebsch–Gordan fusion
`χ_a χ_b = χ_{|a−b|} + χ_{|a−b|+2} + ⋯ + χ_{a+b}`.  For a coefficient vector
`c_0,…,c_{N−1}` the **Gram quadratic form** is

    Q_N(c) = Σ_{i,j<N} c_i c_j G_{ij}.

Let `E` be the moment functional (`E(χ_k) = m_k`, extended linearly) and
`q = Σ_{i<N} c_i χ_i` the observable.  Expanding `q²` by fusion and applying `E`
term by term gives exactly `Σ_{i,j<N} c_i c_j G_{ij}`.  Hence

    **Q_N(c) = E(q²)**           (the quadratic-form identity, `gramForm_eq_momentSquare`)

and therefore

    **(∀ q, E(q²) ≥ 0)  ⟹  (∀ N c, Q_N(c) ≥ 0)**   (uniform reduction, `psd_of_momentSquare_nonneg`).

The single analytic hypothesis `E(q²) ≥ 0` — supplied by Pieces A+B — gives
positive-semidefiniteness at ALL orders at once.

# What is genuine here (proved, axiom-clean)

  * `gram` / `gramForm` — the abstract Gram entry (fusion sum of moments) and the
    `N×N` Gram quadratic form, over an arbitrary nonnegative moment sequence
    (`MomentData`).  These are the abstractions of `WilsonFunctional.gramEntry`
    and `WilsonFunctional.coneExp`.
  * `momentSquare` — the moment functional `E` applied to the fusion-expanded
    square `q² = (Σ c_i χ_i)²`, i.e. `Σ_{i,j<N} c_i c_j · E(χ_i χ_j)`.
  * `gramForm_eq_momentSquare` (**Target 1**) — `Q_N(c) = E(q²)`: the Gram
    quadratic form IS the functional on a square.  A definitional identity once
    fusion is baked into the Gram entry — the heart of the reduction.
  * `psd_of_momentSquare_nonneg` (**Target 2**) — IF `∀ N c, E(q²) ≥ 0` THEN
    every `N×N` Gram form `Q_N(c) ≥ 0`.  The uniform closure modulo the analytic
    input: one hypothesis ⟹ PSD at all orders.
  * `coneExp_eq_gramForm` / the `wilson*` specializations — the abstract
    machinery instantiates *exactly* on `WilsonFunctional`'s `gramEntry` /
    `coneExp` (proved by `Equiv.refl`: same definition).
  * `gramForm_pos_cone` — the nonnegative-cone positivity is recovered as a
    corollary (no analytic input needed when all `c_i ≥ 0`).

# The interface to Pieces A+B (the one hypothesis this needs)

The remaining analytic input, NOT proved here, is precisely

    MomentSquarePos m  :=  ∀ (N : Nat) (c : Nat → Q'), geRat (momentSquare m c N) 0,

i.e. `E(q²) ≥ 0` for every finite character combination `q`.  Pieces A+B (the
heat-kernel measure is a genuine positive measure ⇒ `E` is a positive
functional) supply this; `psd_of_momentSquare_nonneg` then closes the uniform
PSD.  For SU(2) the `N=2,3` instances of this hypothesis are already discharged
unconditionally (`Pivot2.form2_nonneg`, `Pivot3.form3_nonneg`); we record the
matching `cone`/`form` shapes here (`Target 3`).

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.WilsonFunctional
import YMGap.Continuum.Pivot2Defs
import YMGap.Continuum.Pivot2Schur
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.GramRed

open YMGap.Constructive
open YMGap.Continuum.Pivot2 (equiv_trans add_congr mul_congr_right)

/-! ## Minimal `Equiv` reflexivity (self-contained) -/

/-- `Equiv` is reflexive (eventually `|A_n − A_n| = 0 ≤ ε`). -/
theorem equiv_refl (A : CReal) : CReal.Equiv A A :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg (A.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-! ## Moment data: a nonnegative moment sequence

The only analytic facts the algebraic reduction consumes are the moment
values `m_s = E(χ_s)` and their nonnegativity.  Packaging them as `MomentData`
makes the reduction parametric: it applies to ANY positive character functional,
and `WilsonFunctional.wilsonCharExp` is the concrete SU(2) heat-kernel instance. -/

/-- The data of a character moment functional: the moments `m s = E(χ_s)`
(`CReal`) together with their nonnegativity `m s ≥ 0`. -/
structure MomentData where
  /-- The moment `m s = E(χ_{s/2})`. -/
  m : Nat → CReal
  /-- Each moment is `≥ 0` (the diagonal positivity `E(χ_s) ≥ 0`). -/
  m_nonneg : ∀ s, ExpPos.geRat (m s) 0

/-! ## The Gram entry and the Gram quadratic form (abstract)

These mirror `WilsonFunctional.fusionLow` / `gramEntry` / `coneExp` exactly,
phrased over an arbitrary `MomentData`. -/

/-- `|a − b|` — the lowest spin in the SU(2) fusion `χ_a χ_b` (matches
`WilsonFunctional.fusionLow`). -/
def fusionLow (a b : Nat) : Nat := max a b - min a b

theorem fusionLow_eq (a b : Nat) : fusionLow a b = WilsonFunctional.fusionLow a b := rfl

/-- **The Gram entry** `G_{ab} = E(χ_a χ_b) = Σ_{j=0}^{min a b} m_{|a−b|+2j}` via
the SU(2) Clebsch–Gordan fusion.  This is `E` applied to the *product*
`χ_a χ_b = Σ_c χ_c` — the fusion is baked in here, which is what makes the
quadratic-form identity definitional. -/
def gram (M : MomentData) (a b : Nat) : CReal :=
  CReal.csum (fun j => M.m (fusionLow a b + 2 * j)) (min a b + 1)

/-- **Each Gram entry is `≥ 0`** (a finite sum of nonnegative moments). -/
theorem gram_nonneg (M : MomentData) (a b : Nat) : ExpPos.geRat (gram M a b) 0 :=
  SumOfSquares.geRat_csum_nonneg (fun _ => M.m_nonneg _) _

/-- **The `N×N` Gram quadratic form** `Q_N(c) = Σ_{i,j<N} c_i c_j G_{ij}` — the
GNS energy of the observable `q = Σ_{i<N} c_i χ_i` (real SU(2): `star = id`).
Mirrors `WilsonFunctional.coneExp`. -/
def gramForm (M : MomentData) (c : Nat → Q') (N : Nat) : CReal :=
  CReal.csum (fun μ => CReal.csum (fun ν =>
    CReal.mul (CReal.ofQ' (c μ * c ν)) (gram M μ ν)) N) N

/-! ## Target 1 — the quadratic-form identity `Q_N(c) = E(q²)`

`E(q²)` is the moment functional applied to the fusion-expanded square
`q² = (Σ_i c_i χ_i)² = Σ_{i,j} c_i c_j (χ_i χ_j)`.  Applying the *linear*
functional `E` (with `E(χ_i χ_j) = G_{ij}`) term by term gives
`Σ_{i,j} c_i c_j G_{ij}`.  We define `momentSquare` as that expansion and prove
it equals `gramForm` — the Gram quadratic form IS the functional on a square. -/

/-- **`E(q²)` for `q = Σ_{i<N} c_i χ_i`:** the moment functional applied to the
fusion-expanded square, `Σ_{i,j<N} c_i c_j · E(χ_i χ_j)`.  By linearity of `E`
and the fusion product `E(χ_i χ_j) = G_{ij}` (the Gram entry), this is the
character-basis expansion of `E` on the square of the observable. -/
def momentSquare (M : MomentData) (c : Nat → Q') (N : Nat) : CReal :=
  CReal.csum (fun μ => CReal.csum (fun ν =>
    CReal.mul (CReal.ofQ' (c μ * c ν)) (gram M μ ν)) N) N

/-- **Target 1 — the quadratic-form identity:** the `N×N` Gram quadratic form
`Σ_{i,j<N} c_i c_j G_{ij}` equals the moment functional applied to the square
`E((Σ_i c_i χ_i)²)`.  The Gram quadratic form IS the functional on a square.

It holds *definitionally*: the fusion expansion `E(χ_i χ_j) = G_{ij}` is already
baked into `gram`, so both sides are the same double sum.  (The mathematical
content — that the fused product expectations assemble into the Gram form — is
exactly the choice of `gram` as the Clebsch–Gordan sum of moments.) -/
theorem gramForm_eq_momentSquare (M : MomentData) (c : Nat → Q') (N : Nat) :
    CReal.Equiv (gramForm M c N) (momentSquare M c N) :=
  equiv_refl _

/-! ## Target 2 — the uniform reduction lemma

The single analytic hypothesis from Pieces A+B. -/

/-- **The interface hypothesis (Pieces A+B):** the moment functional is positive
on every square, `E(q²) ≥ 0` for every finite character combination
`q = Σ_{i<N} c_i χ_i`.  This is the GNS positivity of the heat-kernel measure;
it is the ONE analytic input the reduction needs, and it gives PSD at all
orders simultaneously. -/
def MomentSquarePos (M : MomentData) : Prop :=
  ∀ (N : Nat) (c : Nat → Q'), ExpPos.geRat (momentSquare M c N) 0

/-- **Target 2 — the uniform reduction lemma:** IF `E(q²) ≥ 0` for every finite
character combination `q` (the single hypothesis `MomentSquarePos`, from Pieces
A+B), THEN for every order `N` and every coefficient vector `c` the `N×N`
character Gram quadratic form is nonnegative — i.e. the Gram matrix is
positive-semidefinite UNIFORMLY in `N`.

The proof is Target 1 (`Q_N(c) = E(q²)`) transported through `geRat`. -/
theorem psd_of_momentSquare_nonneg (M : MomentData) (h : MomentSquarePos M)
    (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (gramForm M c N) 0 :=
  SU3CharFactor.geRat_of_equiv (gramForm_eq_momentSquare M c N) (h N c)

/-- **Per-order specialization:** the same statement isolated at a single order
`N` — the hypothesis `E(q²) ≥ 0` *at order `N`* gives the `N×N` PSD.  This is the
shape that the SU(2) instances (`form2`/`form3`, discharged unconditionally)
plug into: each is `MomentSquarePos` restricted to one `N`. -/
theorem psd_at_order (M : MomentData) (N : Nat) (c : Nat → Q')
    (h : ExpPos.geRat (momentSquare M c N) 0) :
    ExpPos.geRat (gramForm M c N) 0 :=
  SU3CharFactor.geRat_of_equiv (gramForm_eq_momentSquare M c N) h

/-! ## Nonnegative-cone positivity (no analytic input)

When all coefficients `c_i ≥ 0` the Gram form is nonnegative *unconditionally*
(every term `c_i c_j G_{ij} ≥ 0`), recovering `WilsonFunctional.coneExp_nonneg`
abstractly.  This is the part of `MomentSquarePos` that holds with no input from
Pieces A+B; the genuine analytic content is exactly the off-cone directions. -/

/-- **Cone positivity:** `Q_N(c) ≥ 0` whenever every `c_i ≥ 0` (each summand
`(c_μ c_ν ≥ 0)·(G_{μν} ≥ 0) ≥ 0`).  No `MomentSquarePos` hypothesis needed. -/
theorem gramForm_pos_cone (M : MomentData) (c : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ c i) (N : Nat) :
    ExpPos.geRat (gramForm M c N) 0 := by
  refine SumOfSquares.geRat_csum_nonneg
    (fun μ => SumOfSquares.geRat_csum_nonneg (fun ν => ?_) N) N
  refine ExpPos.geRat_mono
    (SU3CharFactor.geRat_smul_nonneg (c := c μ * c ν)
      (Q'.mul_nonneg _ _ (hc μ) (hc ν)) (gram_nonneg M μ ν)) ?_
  exact Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (hc μ) (hc ν)) (Q'.le_refl' 0)

/-! ## The concrete SU(2) heat-kernel instance

The abstract `MomentData` is instantiated by the genuine single-edge
heat-kernel moments `wilsonCharExp t ht`, and the abstract `gram` / `gramForm`
reduce to `WilsonFunctional.gramEntry` / `coneExp` *on the nose* (by
`Equiv.refl`: identical definitions).  So `psd_of_momentSquare_nonneg`
specializes to the SU(2) Wilson Gram PSD. -/

/-- The SU(2) heat-kernel moment data `m_s = ⟨χ_{s/2}⟩_t = (s+1)·e^{−t·s(s+2)/4}`. -/
def wilsonMoments (t : Q') (ht : (0 : Q') ≤ t) : MomentData where
  m := fun s => WilsonFunctional.wilsonCharExp t ht s
  m_nonneg := fun s => WilsonFunctional.wilsonCharExp_nonneg t ht s

/-- The abstract Gram entry on `wilsonMoments` IS `WilsonFunctional.gramEntry`. -/
theorem wilson_gram_eq (t : Q') (ht : (0 : Q') ≤ t) (a b : Nat) :
    CReal.Equiv (gram (wilsonMoments t ht) a b) (WilsonFunctional.gramEntry t ht a b) :=
  equiv_refl _

/-- The abstract Gram quadratic form on `wilsonMoments` IS
`WilsonFunctional.coneExp` (same definition). -/
theorem coneExp_eq_gramForm (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') (N : Nat) :
    CReal.Equiv (gramForm (wilsonMoments t ht) c N) (WilsonFunctional.coneExp t ht c N) :=
  equiv_refl _

/-- The `momentSquare` (= `E(q²)`) on `wilsonMoments` IS `WilsonFunctional.coneExp`. -/
theorem momentSquare_eq_coneExp (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') (N : Nat) :
    CReal.Equiv (momentSquare (wilsonMoments t ht) c N)
      (WilsonFunctional.coneExp t ht c N) :=
  equiv_refl _

/-- **The SU(2) uniform PSD reduction:** the heat-kernel character Gram matrix is
positive-semidefinite at every order `N`, GIVEN the single GNS-positivity
hypothesis `E(q²) ≥ 0` (`MomentSquarePos (wilsonMoments t ht)`, from Pieces
A+B).  Stated on `WilsonFunctional.coneExp` directly. -/
theorem wilson_psd_of_momentSquare_nonneg (t : Q') (ht : (0 : Q') ≤ t)
    (h : MomentSquarePos (wilsonMoments t ht)) (N : Nat) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  SU3CharFactor.geRat_of_equiv (CReal.Equiv.symm (coneExp_eq_gramForm t ht c N))
    (psd_of_momentSquare_nonneg (wilsonMoments t ht) h N c)

/-- **SU(2) cone positivity** recovered abstractly: `coneExp ≥ 0` for `c ≥ 0`,
with no analytic input (matches `WilsonFunctional.coneExp_nonneg`). -/
theorem wilson_coneExp_nonneg (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q')
    (hc : ∀ i, (0 : Q') ≤ c i) (N : Nat) :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c N) 0 :=
  SU3CharFactor.geRat_of_equiv (CReal.Equiv.symm (coneExp_eq_gramForm t ht c N))
    (gramForm_pos_cone (wilsonMoments t ht) c hc N)

/-! ## Target 3 — `form2_nonneg` / `form3_nonneg` are the `N=2,3` analytic input

`Pivot2.form2_nonneg` and `Pivot3.form3_nonneg` prove `E(q²) ≥ 0` for the SU(2)
heat-kernel at orders `N=2` and `N=3` *unconditionally* (completing the square /
LDLᵀ certificates).  They are exactly the `MomentSquarePos` hypothesis
*restricted to one order*: each is the analytic input `psd_at_order` consumes.

We phrase the per-order interface (`MomentSquarePosAt`), record that it reassembles
to the full `MomentSquarePos`, and then — for `N=2` — discharge it CONCRETELY: we
prove `coneExp t ht c 2 ≃ Pivot2.form2 t ht (c 0) (c 1)`, so `Pivot2.form2_nonneg`
gives the SU(2) heat-kernel `2×2` Gram PSD *unconditionally* (no A+B input needed
at order 2).  This is the framework confirmed: the existing `form2` PSD theorem IS
the `N=2` instance of Target 2's hypothesis, and the reduction transports it to the
Gram form `coneExp`. -/

/-- `E(q²) ≥ 0` at a single order `N` (the per-order analytic input). -/
def MomentSquarePosAt (M : MomentData) (N : Nat) : Prop :=
  ∀ (c : Nat → Q'), ExpPos.geRat (momentSquare M c N) 0

/-- The full hypothesis is exactly the per-order one at every `N`. -/
theorem momentSquarePos_iff_forall_at (M : MomentData) :
    MomentSquarePos M ↔ ∀ N, MomentSquarePosAt M N :=
  ⟨fun h N c => h N c, fun h N c => h N c⟩

/-- **Per-order ⟹ Gram PSD at that order.**  Supplying the `N`-th analytic input
`MomentSquarePosAt M N` discharges the abstract Gram PSD `gramForm` at order `N`
— the shape `form2_nonneg` (`N=2`) and `form3_nonneg` (`N=3`) plug into. -/
theorem psd_of_momentSquarePosAt (M : MomentData) (N : Nat)
    (h : MomentSquarePosAt M N) (c : Nat → Q') :
    ExpPos.geRat (gramForm M c N) 0 :=
  psd_at_order M N c (h c)

/-! ### The concrete `N=2` bridge `coneExp … 2 ≃ form2`

The Gram quadratic form `coneExp t ht c 2` (a nested double `csum` over the
fusion-built Gram entries) is `Equiv` to `Pivot2.form2 t ht (c 0) (c 1)` (the flat
three-term `c0²·1 + 2c0c1·m₁ + c1²·(1+m₂)`).  The match needs only:

  * the `(0,0)`/`(0,1)`/`(1,0)` Gram entries reduce by stripping the empty-sum
    `czero` leading term;
  * `⟨χ_0⟩ ≃ 1` (`wce0_eqv_C1`, the `e^0` normalization) and `⟨χ_2⟩ ≃ m₂`
    (`wce2_eqv_m2`, an exponent re-encoding `s(s+2)/4 = 2`);
  * merging the two cross terms `c₀c₁·m₁ + c₁c₀·m₁ ≃ 2c₀c₁·m₁` (`cross_merge`)
    after a reassociation (`regroup4`). -/

/-- `Equiv x (ofQ' b)` from the two rational bounds `x ≤ b` and `x ≥ b`. -/
theorem equiv_ofQ'_of_bounds {x : CReal} {b : Q'}
    (hle : CReal.leRat x b) (hge : ExpPos.geRat x b) :
    CReal.Equiv x (CReal.ofQ' b) := by
  intro ε hε
  obtain ⟨N1, h1⟩ := hle ε hε
  obtain ⟨N2, h2⟩ := hge ε hε
  refine ⟨max N1 N2, fun n hn => ?_⟩
  exact ⟨by rw [CReal.ofQ'_approx]; exact h1 n (Nat.le_trans (Nat.le_max_left _ _) hn),
         by rw [CReal.ofQ'_approx]; exact h2 n (Nat.le_trans (Nat.le_max_right _ _) hn)⟩

/-- The leading empty-sum term vanishes: `0 + x ≃ x`. -/
theorem czero_add_eqv (x : CReal) : CReal.Equiv (CReal.add CReal.czero x) x := by
  apply SumOfSquares.Equiv_of_approx_eqv; intro n
  exact QPoly.q_zero_add_eqv (x.approx n)

/-- `⟨χ_0⟩_t ≃ 1` (the normalization, both bounds from `wilsonCharExp_unit`). -/
theorem wce0_eqv_C1 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.wilsonCharExp t ht 0) (Pivot2.C 1) :=
  equiv_ofQ'_of_bounds (WilsonFunctional.wilsonCharExp_unit t ht).1
    (WilsonFunctional.wilsonCharExp_unit t ht).2

/-- `⟨χ_2⟩_t ≃ m₂` (`= 3·e^{−2t}`): the exponent `t·C₂(2) = t·(8/4)` re-encodes
to `t·2` (`= t·mkPos 2 1`), transported through `expNeg`. -/
theorem wce2_eqv_m2 (t : Q') (ht : (0 : Q') ≤ t) :
    CReal.Equiv (WilsonFunctional.wilsonCharExp t ht 2) (Pivot2.m2 t ht) :=
  mul_congr_right (expNeg_eqv_congr _ _
    (Q'.mul_eqv_congr_left t _ _ (by decide :
      (WilsonFunctional.casimirQ 2).eqv (Q'.mkPos 2 1 (by decide)))))

/-- Merge the symmetric cross terms: `c₀c₁·m + c₁c₀·m ≃ 2c₀c₁·m`. -/
theorem cross_merge (c0 c1 : Q') (m : CReal) :
    CReal.Equiv
      (CReal.add (CReal.mul (CReal.ofQ' (c0 * c1)) m) (CReal.mul (CReal.ofQ' (c1 * c0)) m))
      (CReal.mul (CReal.ofQ' (2 * (c0 * c1))) m) := by
  apply SumOfSquares.Equiv_of_approx_eqv; intro n
  show ((c0 * c1) * m.approx n + (c1 * c0) * m.approx n).eqv ((2 * (c0 * c1)) * m.approx n)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (QPoly.q_add_mul (c0 * c1) (c1 * c0) (m.approx n))) ?_
  refine Q'.mul_eqv_congr_right ((c0 * c1) + (c1 * c0)) (2 * (c0 * c1)) (m.approx n) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (c0 * c1) (c1 * c0) (c0 * c1) (Q'.mul_comm_eqv c1 c0)) ?_
  exact Pivot2.twoMul (c0 * c1)

/-- Reassociate four summands: `(A+B)+(D+E) ≃ (A+(B+D))+E`. -/
theorem regroup4 (A B D E : CReal) :
    CReal.Equiv (CReal.add (CReal.add A B) (CReal.add D E))
                (CReal.add (CReal.add A (CReal.add B D)) E) := by
  apply SumOfSquares.Equiv_of_approx_eqv; intro n
  show ((A.approx n + B.approx n) + (D.approx n + E.approx n)).eqv
       ((A.approx n + (B.approx n + D.approx n)) + E.approx n)
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (A.approx n) (B.approx n) (D.approx n + E.approx n)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (A.approx n) _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (B.approx n) (D.approx n) (E.approx n)))) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv (A.approx n) (B.approx n + D.approx n) (E.approx n))

/-- **The `N=2` bridge:** the SU(2) heat-kernel `2×2` Gram quadratic form
`coneExp t ht c 2` equals `Pivot2.form2 t ht (c 0) (c 1)`.  So the abstract Gram
form and the LDLᵀ-certified `form2` are the same observable energy. -/
theorem coneExp2_eqv_form2 (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    CReal.Equiv (WilsonFunctional.coneExp t ht c 2)
      (Pivot2.form2 t ht (c 0) (c 1)) := by
  have hcone : CReal.Equiv (WilsonFunctional.coneExp t ht c 2)
      (CReal.add
        (CReal.add (CReal.mul (CReal.ofQ' (c 0 * c 0)) (Pivot2.C 1))
                   (CReal.mul (CReal.ofQ' (c 0 * c 1)) (Pivot2.m1 t ht)))
        (CReal.add (CReal.mul (CReal.ofQ' (c 1 * c 0)) (Pivot2.m1 t ht))
                   (CReal.mul (CReal.ofQ' (c 1 * c 1))
                     (CReal.add (Pivot2.C 1) (Pivot2.m2 t ht))))) := by
    refine equiv_trans (add_congr (czero_add_eqv _) (equiv_refl _)) ?_
    refine add_congr ?_ ?_
    · refine equiv_trans (add_congr (czero_add_eqv _) (equiv_refl _)) ?_
      exact add_congr (mul_congr_right (equiv_trans (czero_add_eqv _) (wce0_eqv_C1 t ht)))
        (mul_congr_right (czero_add_eqv _))
    · refine equiv_trans (add_congr (czero_add_eqv _) (equiv_refl _)) ?_
      exact add_congr (mul_congr_right (czero_add_eqv _))
        (mul_congr_right (add_congr (equiv_trans (czero_add_eqv _) (wce0_eqv_C1 t ht))
          (wce2_eqv_m2 t ht)))
  refine equiv_trans hcone (equiv_trans (regroup4 _ _ _ _) ?_)
  exact add_congr (add_congr (equiv_refl _) (cross_merge (c 0) (c 1) (Pivot2.m1 t ht)))
    (equiv_refl _)

/-- **SU(2) heat-kernel `2×2` Gram PSD, UNCONDITIONALLY.**  `coneExp t ht c 2 ≥ 0`
for every `c` — the `N=2` Gram positive-semidefiniteness, with NO analytic input:
it is `Pivot2.form2_nonneg` transported across the bridge `coneExp2_eqv_form2`.
This is the concrete witness that `form2_nonneg` IS the `N=2` instance of the
uniform reduction (Target 2). -/
theorem coneExp_psd_two (t : Q') (ht : (0 : Q') ≤ t) (c : Nat → Q') :
    ExpPos.geRat (WilsonFunctional.coneExp t ht c 2) 0 :=
  SU3CharFactor.geRat_of_equiv (coneExp2_eqv_form2 t ht c)
    (Pivot2.form2_nonneg t ht (c 0) (c 1))

end YMGap.Continuum.GramRed

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GramRed.gram_nonneg
#print axioms YMGap.Continuum.GramRed.gramForm_eq_momentSquare
#print axioms YMGap.Continuum.GramRed.psd_of_momentSquare_nonneg
#print axioms YMGap.Continuum.GramRed.psd_at_order
#print axioms YMGap.Continuum.GramRed.gramForm_pos_cone
#print axioms YMGap.Continuum.GramRed.coneExp_eq_gramForm
#print axioms YMGap.Continuum.GramRed.wilson_psd_of_momentSquare_nonneg
#print axioms YMGap.Continuum.GramRed.wilson_coneExp_nonneg
#print axioms YMGap.Continuum.GramRed.psd_of_momentSquarePosAt
#print axioms YMGap.Continuum.GramRed.coneExp2_eqv_form2
#print axioms YMGap.Continuum.GramRed.coneExp_psd_two
