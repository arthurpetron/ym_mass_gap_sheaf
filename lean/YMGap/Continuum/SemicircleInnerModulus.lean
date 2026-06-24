/-
# The index-indexed inner regularity modulus for the semicircle Riemann sequence

This module discharges the inner-modulus residual of the semicircle convergence
analysis at the CORRECT interface — the index-indexed one
(`Constructive.CReal.ModCauchyIdx`) — rather than the structurally-uninhabitable
index-FREE one.

## The setting and the obstruction

`seqSemi i = semiSum (i+1)` is a `csum` of `i+1` scaled Heron-√ terms
`(2/(i+1))·√(1 − x_j²)`.  Its approximation unfolds (proved in
`SemicircleConverge.seqSemi_approx_eq`) to the rational finite sum

    (seqSemi i).approx k = Σ_{j<i+1} (2/(i+1)) · heronSeq (1 − x_j²) k .

Each term is a regular `CReal` with its OWN Cauchy modulus
(`Constructive.CReal.sqrtModulus`).  Because the number of terms `i+1` grows with
`i`, NO single index-free inner modulus `reg : Q' → Nat` works for every term
simultaneously: this is the sharp structural obstruction recorded as the named
residual `SemicircleConverge.UniformInnerModulus` (which is therefore genuinely
uninhabitable as literally stated).

## What is PROVED here (axiom-clean, GENUINE new content)

  * `maxBelow` / `le_maxBelow` — the running max of a `Nat`-valued function over
    `j < n`, dominating each entry.
  * `nodeMod` — the per-term (`j`-indexed) inner modulus, the genuine
    `sqrtModulus` of the node radicand `1 − x_j²` at lower-bound witness `1/n`.
  * `node_two_sided` — the two-sided per-node Heron-iterate regularity
    `|heronSeq(1−x_j²)_p − heronSeq(1−x_j²)_q| ≤ ε'` for `p,q ≥ nodeMod`, from the
    proved per-√ directed modulus `sqrt_cauchy_dir`.
  * `seqSemi_regularIdx` — **the index-indexed inner regularity modulus**: an
    explicit `reg : Nat → Q' → Nat` with
    `∀ i ε>0, ∀ p q ≥ reg i ε, |(seqSemi i).approx p − (seqSemi i).approx q| ≤ ε`.
    The `(i+1)` term count is absorbed by the weight `2/(i+1)` (the per-term
    error `(2/(i+1))·ε'` summed `i+1` times is `≤ 2·ε' = ε`).  This is genuine
    Type-level data.
  * `UniformInnerModulusIdx` / `seqSemi_uniformInnerModulusIdx` — the
    index-indexed analog of `SemicircleConverge.UniformInnerModulus`, DISCHARGED
    by `seqSemi_regularIdx`.  This is exactly the `ModCauchyIdx.regular` field for
    `seqSemi`; it is the structural-residual discharge the index-indexed
    completeness backbone (`Constructive.CReal.completeLimitIdx`) consumes.

## What remains (the single residual for full semicircle convergence)

  * The OUTER Riemann bound `SemicircleConverge.UniformRiemannBound`
    (`ModCauchy.bound`/`ModCauchyIdx.bound` — IDENTICAL between the two
    interfaces, the genuine convergence content): the cell-matching Riemann
    estimate assembling the proved per-cell √-Hölder bound
    (`SemicircleConverge.nodeWeight_holder`) into the index-uniform sum bound.
    With the OUTER bound plus this inner modulus, `completeLimitIdx seqSemi` is
    the genuine `semiInt`.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  PROVED: the index-indexed inner modulus and its discharge.
NAMED-open: the outer Riemann bound.  Axiom-gate: `[propext]`/`[propext,
Quot.sound]`.
-/

import YMGap.Continuum.SemicircleConverge
import YMGap.Constructive.CRealCompleteIdx
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SemicircleInnerModulus

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleConverge
open YMGap.Constructive.RationalTail

/-! ## 1. Running max over `j < n` -/

/-- The running max of `f 0, …, f (n−1)` (with `maxBelow f 0 = 0`). -/
def maxBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => max (maxBelow f n) (f n)

/-- Each entry `f j` for `j < n` is dominated by `maxBelow f n`. -/
theorem le_maxBelow (f : Nat → Nat) : ∀ {n j : Nat}, j < n → f j ≤ maxBelow f n
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, hj => by
    rcases Nat.lt_or_ge j n with hlt | hge
    · exact Nat.le_trans (le_maxBelow f hlt) (Nat.le_max_left _ _)
    · have hjn : j = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hge
      cases hjn; exact Nat.le_max_right _ _

/-! ## 2. The per-node (index-`j`) inner modulus -/

/-- The per-term inner modulus for resolution `n` (`n = i+1`), node index `j`,
tolerance `ε'`: the genuine `sqrtModulus` of `1 − x_j²` at the witness `1/n` when
`j < n`, else `0`. -/
def nodeMod (n : Nat) (hn : 0 < n) (ε' : Q') (hε' : (0 : Q') < ε') (j : Nat) : Nat :=
  if hj : j < n then
    CReal.sqrtModulus (oneMinusSqNode n j hn hj) (nodeLB n hn)
      (oneMinusSqNode_pos hn hj) (nodeLB_pos hn) ε' hε'
  else 0

/-- **Two-sided per-node Heron regularity.**  For `j < n` and approx indices
`p, q ≥ nodeMod n hn ε' hε' j`, the Heron iterates of the node radicand `1 − x_j²`
agree to within `ε'` (both directions), from the per-√ directed modulus
`sqrt_cauchy_dir`. -/
theorem node_two_sided (n : Nat) (hn : 0 < n) (ε' : Q') (hε' : (0 : Q') < ε')
    {j : Nat} (hj : j < n) {p q : Nat}
    (hp : nodeMod n hn ε' hε' j ≤ p) (hq : nodeMod n hn ε' hε' j ≤ q) :
    CReal.heronSeq (oneMinusSqNode n j hn hj) p
        ≤ CReal.heronSeq (oneMinusSqNode n j hn hj) q + ε'
      ∧ CReal.heronSeq (oneMinusSqNode n j hn hj) q
        ≤ CReal.heronSeq (oneMinusSqNode n j hn hj) p + ε' := by
  have hmod : nodeMod n hn ε' hε' j
      = CReal.sqrtModulus (oneMinusSqNode n j hn hj) (nodeLB n hn)
          (oneMinusSqNode_pos hn hj) (nodeLB_pos hn) ε' hε' := by
    unfold nodeMod; rw [dif_pos hj]
  rw [hmod] at hp hq
  rcases Nat.le_total q p with hqp | hpq
  · refine ⟨?_, ?_⟩
    · -- heron p ≤ heron q + ε' : antitone (q ≤ p ⇒ heron p ≤ heron q) then add ε'
      refine Q'.le_trans' _ _ _
        (CReal.heronSeq_antitone (oneMinusSqNode n j hn hj) (oneMinusSqNode_pos hn hj) hqp) ?_
      exact Q'.add_le_self_of_nonneg _ ε' (Q'.le_of_lt hε')
    · -- heron q ≤ heron p + ε' : sqrt_cauchy_dir with q ≥ modulus, q ≤ p
      exact CReal.sqrt_cauchy_dir (oneMinusSqNode n j hn hj) (nodeLB n hn)
        (oneMinusSqNode_pos hn hj) (nodeLB_pos hn) (nodeLB_sq_le hn hj) ε' hε' hq hqp
  · refine ⟨?_, ?_⟩
    · -- heron p ≤ heron q + ε' : sqrt_cauchy_dir with p ≥ modulus, p ≤ q
      exact CReal.sqrt_cauchy_dir (oneMinusSqNode n j hn hj) (nodeLB n hn)
        (oneMinusSqNode_pos hn hj) (nodeLB_pos hn) (nodeLB_sq_le hn hj) ε' hε' hp hpq
    · -- heron q ≤ heron p + ε' : antitone (p ≤ q ⇒ heron q ≤ heron p) then add ε'
      refine Q'.le_trans' _ _ _
        (CReal.heronSeq_antitone (oneMinusSqNode n j hn hj) (oneMinusSqNode_pos hn hj) hpq) ?_
      exact Q'.add_le_self_of_nonneg _ ε' (Q'.le_of_lt hε')

/-! ## 3. The scaled-weight two-sided bound

The explicit `j`-th term of `(seqSemi (n−1)).approx k` is
`(2/n)·heronSeq(1−x_j²)_k`.  We express it via `nodeWeight` (PUBLIC), matching the
public definition `semiSum n = csum (fun j => mul (ofQ' (2/n)) (nodeWeight n j))`. -/

/-- The explicit scaled per-node weight value, in terms of the PUBLIC
`nodeWeight`: `(mul (ofQ' (2/n)) (nodeWeight n j)).approx k = (2/n)·heronSeq_k`
for `j < n`. -/
private theorem mulWeight_approx_eq (n : Nat) (hn : 0 < n) {j : Nat} (hj : j < n) (k : Nat) :
    (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx k
      = lebW n hn * CReal.heronSeq (oneMinusSqNode n j hn hj) k := by
  show (CReal.ofQ' (lebW n hn)).approx k * (nodeWeight n hn j).approx k
      = lebW n hn * CReal.heronSeq (oneMinusSqNode n j hn hj) k
  rw [CReal.ofQ'_approx]
  have hnode : (nodeWeight n hn j).approx k
      = CReal.heronSeq (oneMinusSqNode n j hn hj) k := by
    unfold nodeWeight
    rw [dif_pos hj, CReal.sqrtFrom_approx]
  rw [hnode]

/-- **Per-term scaled two-sided bound.**  For `j < n` and `p,q ≥ nodeMod n hn ε'
j`, the scaled weights agree to within `(2/n)·ε'`. -/
private theorem mulWeight_two_sided (n : Nat) (hn : 0 < n) (ε' : Q') (hε' : (0 : Q') < ε')
    {j : Nat} (hj : j < n) {p q : Nat}
    (hp : nodeMod n hn ε' hε' j ≤ p) (hq : nodeMod n hn ε' hε' j ≤ q) :
    (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx p
        ≤ (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx q + lebW n hn * ε'
      ∧ (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx q
        ≤ (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx p + lebW n hn * ε' := by
  obtain ⟨h1, h2⟩ := node_two_sided n hn ε' hε' hj hp hq
  have hwnn : (0 : Q') ≤ lebW n hn := lebW_nonneg hn
  rw [mulWeight_approx_eq n hn hj p, mulWeight_approx_eq n hn hj q]
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (lebW n hn) h1 hwnn) ?_
    exact Q'.le_of_eqv (Q'.mul_add_eqv (lebW n hn) _ ε')
  · refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (lebW n hn) h2 hwnn) ?_
    exact Q'.le_of_eqv (Q'.mul_add_eqv (lebW n hn) _ ε')

/-! ## 4. Summing the constant scaled error: `Σ_{j<n} (2/n)·ε' ≤ 2·ε'` -/

/-- `Σ_{j<n} (2/n)·ε' ≃ (Σ_{j<n} 2/n)·ε' ≤ 2·ε'`. -/
private theorem finSum_const_scaled_le (n : Nat) (hn : 0 < n) (ε' : Q') (hε' : (0 : Q') < ε') :
    RationalTail.finSum (fun _ => lebW n hn * ε') n ≤ (2 : Q') * ε' := by
  -- Σ (w·ε') ≃ (Σ w)·ε'  (finSum_mul_const, reversed)
  have heqv : (RationalTail.finSum (fun _ => lebW n hn) n * ε').eqv
      (RationalTail.finSum (fun _ => lebW n hn * ε') n) :=
    RationalTail.finSum_mul_const (fun _ => lebW n hn) ε' n
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv) ?_
  -- (Σ w)·ε' ≤ 2·ε'
  exact Q'.mul_le_mul_of_nonneg_right _ _ ε'
    (finSum_lebW_le_two n hn) (Q'.le_of_lt hε')

/-- **Explicit `.approx` unfolding via the PUBLIC `nodeWeight`.**  `seqSemi i =
semiSum (i+1)` and `semiSum n = csum (fun j => mul (ofQ' (2/n)) (nodeWeight n j))
n` (definitional), so `csum_approx` gives the rational finite sum of the public
scaled weights. -/
private theorem seqSemi_approx_mul (i : Nat) (k : Nat) :
    (seqSemi i).approx k
      = RationalTail.finSum
          (fun j => (CReal.mul (CReal.ofQ' (lebW (i + 1) (Nat.succ_pos i)))
            (nodeWeight (i + 1) (Nat.succ_pos i) j)).approx k) (i + 1) := by
  show (CReal.csum (fun j => CReal.mul (CReal.ofQ' (lebW (i + 1) (Nat.succ_pos i)))
        (nodeWeight (i + 1) (Nat.succ_pos i) j)) (i + 1)).approx k
      = RationalTail.finSum
          (fun j => (CReal.mul (CReal.ofQ' (lebW (i + 1) (Nat.succ_pos i)))
            (nodeWeight (i + 1) (Nat.succ_pos i) j)).approx k) (i + 1)
  exact CReal.csum_approx _ (i + 1) k

/-! ## 5. The index-indexed inner modulus for `seqSemi` -/

/-- The index-indexed inner modulus: at resolution index `i` (term `seqSemi i =
semiSum (i+1)`) and tolerance `ε`, the running max over the `i+1` nodes of the
per-node `sqrtModulus` at the half-tolerance `ε' = ½ε`.  This is the genuine
`Type`-level inner regularity modulus for the GROWING-modulus Riemann sequence. -/
def seqSemiReg (i : Nat) (ε : Q') : Nat :=
  if hε : (0 : Q') < ε then
    maxBelow (nodeMod (i + 1) (Nat.succ_pos i) (half * ε) (ExpNeg.half_mul_pos ε hε)) (i + 1)
  else 0

/-- **The index-indexed inner regularity of `seqSemi`.**  For every term index `i`
and tolerance `ε > 0`, the approximations of the single term `seqSemi i` agree to
within `ε` past the stage `seqSemiReg i ε` — with the modulus carried as explicit
`Type`-level data (no `Classical`, no Prop-`∃`).  The growing `(i+1)` term count
is absorbed by the weight `2/(i+1)`: the per-term error `(2/(i+1))·(½ε)` summed
`i+1` times is `≤ 2·(½ε) = ε`. -/
theorem seqSemi_regularIdx (i : Nat) (ε : Q') (hε : (0 : Q') < ε) (p q : Nat)
    (hp : seqSemiReg i ε ≤ p) (hq : seqSemiReg i ε ≤ q) :
    (seqSemi i).approx p ≤ (seqSemi i).approx q + ε
      ∧ (seqSemi i).approx q ≤ (seqSemi i).approx p + ε := by
  let n : Nat := i + 1
  have hn : 0 < n := Nat.succ_pos i
  let ε' : Q' := half * ε
  have hε' : (0 : Q') < ε' := ExpNeg.half_mul_pos ε hε
  -- unfold the modulus stage
  have hstage : seqSemiReg i ε = maxBelow (nodeMod n hn ε' hε') n := by
    unfold seqSemiReg; rw [dif_pos hε]
  rw [hstage] at hp hq
  -- unfold the approximations to rational finite sums of the public scaled weights
  have hap : (seqSemi i).approx p
      = RationalTail.finSum
          (fun j => (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx p) n :=
    seqSemi_approx_mul i p
  have haq : (seqSemi i).approx q
      = RationalTail.finSum
          (fun j => (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx q) n :=
    seqSemi_approx_mul i q
  -- `2·ε' ≃ ε`, i.e. `(2:Q')·(½ε) ≃ ε` (via `(2·½) ≃ 1`)
  have htwo_eps : ((2 : Q') * ε').eqv ε := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 2 half ε)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right ((2 : Q') * half) (1 : Q') ε (by decide)) ?_
    exact Q'.one_mul_eqv ε
  -- forward direction: Σ termVal·p ≤ Σ termVal·q + ε
  have key : ∀ (F G : Nat → Q'),
      (∀ j, j < n → F j ≤ G j + lebW n hn * ε') →
      RationalTail.finSum F n ≤ RationalTail.finSum G n + ε := by
    intro F G hFG
    -- F j ≤ (G j + w·ε') for j < n ; finSum F ≤ finSum (G + const) = finSum G + Σ const ≤ finSum G + ε
    -- bound finSum F by finSum (fun j => G j + w·ε')
    have hle : RationalTail.finSum F n
        ≤ RationalTail.finSum (fun j => G j + lebW n hn * ε') n := by
      -- termwise comparison needs j < n; reindex via a length-respecting argument
      -- prove the strengthened statement by induction on the partial length
      have step : ∀ m, m ≤ n →
          RationalTail.finSum F m
            ≤ RationalTail.finSum (fun j => G j + lebW n hn * ε') m := by
        intro m
        induction m with
        | zero => intro _; exact Q'.le_refl' 0
        | succ t ih =>
          intro htn
          have htn' : t ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htn)
          have htlt : t < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) htn
          show RationalTail.finSum F t + F t
              ≤ RationalTail.finSum (fun j => G j + lebW n hn * ε') t + (G t + lebW n hn * ε')
          exact Q'.le_trans' _ _ _
            (Q'.add_le_add_left (RationalTail.finSum F t) (F t) (G t + lebW n hn * ε')
              (hFG t htlt))
            (Q'.add_le_add_right (RationalTail.finSum F t)
              (RationalTail.finSum (fun j => G j + lebW n hn * ε') t)
              (G t + lebW n hn * ε') (ih htn'))
      exact step n (Nat.le_refl n)
    -- finSum (G + const) = finSum G + Σ const
    have hsplit : (RationalTail.finSum (fun j => G j + lebW n hn * ε') n).eqv
        (RationalTail.finSum G n + RationalTail.finSum (fun _ => lebW n hn * ε') n) :=
      RationalTail.finSum_add G (fun _ => lebW n hn * ε') n
    refine Q'.le_trans' _ _ _ hle ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    -- finSum G + Σ const ≤ finSum G + 2·ε' = finSum G + ε
    refine Q'.add_le_add_left (RationalTail.finSum G n) _ ε ?_
    refine Q'.le_trans' _ _ _ (finSum_const_scaled_le n hn ε' hε') ?_
    -- 2·ε' ≃ ε
    exact Q'.le_of_eqv htwo_eps
  refine ⟨?_, ?_⟩
  · rw [hap, haq]
    refine key
      (fun j => (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx p)
      (fun j => (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx q) ?_
    intro j hj
    exact (mulWeight_two_sided n hn ε' hε' hj
      (Nat.le_trans (le_maxBelow _ hj) hp) (Nat.le_trans (le_maxBelow _ hj) hq)).1
  · rw [hap, haq]
    refine key
      (fun j => (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx q)
      (fun j => (CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn j)).approx p) ?_
    intro j hj
    exact (mulWeight_two_sided n hn ε' hε' hj
      (Nat.le_trans (le_maxBelow _ hj) hp) (Nat.le_trans (le_maxBelow _ hj) hq)).2

/-! ## 6. The discharge of the (index-indexed) inner-modulus residual -/

/-- **The index-indexed inner-modulus residual** (the correct analog of
`SemicircleConverge.UniformInnerModulus`): a Type-level inner regularity modulus
`reg : Nat → Q' → Nat` whose `reg i` is a Cauchy modulus for the single term
`seqSemi i`.  This is exactly the `ModCauchyIdx.regular` obligation for
`seqSemi`. -/
def UniformInnerModulusIdx : Type :=
  Σ' reg : Nat → Q' → Nat,
    ∀ i : Nat, ∀ ε : Q', (0 : Q') < ε → ∀ p qq : Nat, reg i ε ≤ p → reg i ε ≤ qq →
      (seqSemi i).approx p ≤ (seqSemi i).approx qq + ε
        ∧ (seqSemi i).approx qq ≤ (seqSemi i).approx p + ε

/-- **`UniformInnerModulusIdx` is DISCHARGED** by the explicit index-indexed
modulus `seqSemiReg` and its regularity `seqSemi_regularIdx`.  This closes the
inner-modulus structural residual of the semicircle convergence at the
index-indexed interface. -/
def seqSemi_uniformInnerModulusIdx : UniformInnerModulusIdx :=
  ⟨seqSemiReg, fun i ε hε p qq hp hqq => seqSemi_regularIdx i ε hε p qq hp hqq⟩

end YMGap.Continuum.SemicircleInnerModulus

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `maxBelow` / `le_maxBelow` — running max over `j < n`.
  * `nodeMod` / `node_two_sided` — the per-node genuine `sqrtModulus` and its
    two-sided Heron-iterate regularity (from `sqrt_cauchy_dir`).
  * `seqSemi_regularIdx` — the index-indexed inner regularity modulus for the
    growing-modulus Riemann sequence `seqSemi` (the `(i+1)` term count absorbed
    by the weight `2/(i+1)`), genuine Type-level data.
  * `UniformInnerModulusIdx` / `seqSemi_uniformInnerModulusIdx` — the
    index-indexed inner-modulus residual, DISCHARGED.  This is the
    `ModCauchyIdx.regular` field for `seqSemi`.

**NAMED-open (the single remaining residual for full semicircle convergence).**
  * The OUTER Riemann bound `SemicircleConverge.UniformRiemannBound`
    (`ModCauchy.bound` = `ModCauchyIdx.bound`, identical between interfaces): the
    cell-matching combinatorics assembling the proved per-cell √-Hölder bound
    `SemicircleConverge.nodeWeight_holder` into the index-uniform sum estimate.
    With it plus this inner modulus, `Constructive.CReal.completeLimitIdx seqSemi`
    is the genuine `semiInt`.

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.SemicircleInnerModulus.le_maxBelow
#print axioms YMGap.Continuum.SemicircleInnerModulus.node_two_sided
#print axioms YMGap.Continuum.SemicircleInnerModulus.seqSemi_regularIdx
#print axioms YMGap.Continuum.SemicircleInnerModulus.seqSemi_uniformInnerModulusIdx
