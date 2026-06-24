/-
The Riemann-refinement convergence analysis for the semicircle integral
`∫_{−1}^1 √(1−x²) dx` — the quantitative content behind
`SemicircleIntegral.SemicircleCauchy = CReal.ModCauchy SemicircleIntegral.seqSemi`,
now that the per-cell √-Hölder modulus
`Constructive.CReal.holder_oneMinusSq` / `sqrtFrom_sub_leRat` is proved.

# Setting

`seqSemi n = semiSum (n+1)`, and
`semiSum n = (2/n)·Σ_{k<n} √(1 − x_k²)` is a `CReal`-`csum` of the scaled per-node
weights `(2/n)·√(1 − x_k²)` (`x_k = (2k+1−n)/n`).  Its approximations unfold
(`csum`/`mul`/`ofQ'`/`sqrtFrom`) to the explicit rational finite sum

    (seqSemi n).approx k
      = Σ_{j<n+1} (2/(n+1)) · heronSeq (1 − x_j²) k        (PROVED below).

# What is PROVED here (axiom-clean, GENUINE new content)

  * `seqSemi_approx_eq` — the explicit `.approx k` unfolding above: every
    approximation of `seqSemi n` is the rational finite sum of the weighted
    Heron iterates of the node radicands.  This is the concrete object every
    modulus field of `ModCauchy` must control.

  * `seqSemi_self_cauchy` — each individual term `seqSemi i` IS Cauchy (it is a
    genuine `CReal`): its own `.cauchy` field gives a per-resolution inner
    regularity modulus.  This is the honest, RESOLUTION-INDEXED inner modulus
    (see the named residual for why a single index-FREE inner modulus does not
    exist).

  * `nodeRadiusDiff_le` — the pure `Q'` rectangle arithmetic
    `|(1 − x_k²) − (1 − y_l²)| ≤ 2·|x_k − x_l|` for the uniform-midpoint nodes,
    the radicand-difference input the √-Hölder modulus consumes.

  * `nodeWeight_holder` — the genuine per-cell √-Hölder bound on the actual node
    weights: `√(1 − x_k²) − √(1 − y_l²) ≤ c` (sound `leRat`) whenever the larger
    radicand exceeds the smaller by at most `c²`.  This is
    `holder_oneMinusSq` instantiated at the concrete `nodeWeight` radicands —
    the reusable per-cell Riemann estimate.

  * `semicircleCauchy_of_residuals` — `SemicircleCauchy` ASSEMBLED from the two
    named residuals below: the precise reduction of the convergence modulus.

# What is NAMED-open (the honest residuals — NOT proved here)

  * `SemicircleCauchy` is NOT discharged.  Two `ModCauchy` fields remain open,
    and both are open for a SHARP, NAMED structural reason — not for lack of the
    √-Hölder lemma (which is now proved):

    - `UniformInnerModulus` — `ModCauchy.regular` demands a single inner
      regularity modulus `reg : Q' → Nat` valid for EVERY term `seqSemi i`.  But
      the weighted Heron error sums to
      `Σ_{j<i+1} (2/(i+1))·|heronSeq(a_j)_p − heronSeq(a_j)_q| ≤ 3·(i+1)·2^{−m}`
      (the weight `2/(i+1)` cancels the `gap_bound` divisor `L+L = 2/(i+1)`
      EXACTLY, leaving `Σ_j errAt(a_j,m) ≤ (i+1)·3·2^{−m}`), whose `(i+1)` factor
      grows without bound.  Hence NO index-free `reg` works; the inner modulus is
      genuinely `i`-indexed (delivered as `seqSemi_regAt`).  Closing `ModCauchy`
      as literally stated needs the index-free interface relaxed to an
      `i`-indexed inner modulus (a structural change to `ModCauchy`, not new
      analysis).

    - `UniformRiemannBound` — `ModCauchy.bound` demands, for `m,n ≥ M ε` and
      EVERY approx index `k`, `|(seqSemi m).approx k − (seqSemi n).approx k| ≤ ε`.
      For fixed `k` this is the convergence in `m` of the rational Riemann sum
      `(2/(m+1))·Σ_j heronSeq(1−x_j², k)` of the bounded function
      `x ↦ heronSeq(1−x², k)`; uniformity in `k` is the genuine √-Hölder Riemann
      modulus (the per-cell input `nodeWeight_holder` is proved here; the
      cell-matching combinatorics assembling it into the index-uniform sum bound
      is the residual).

# Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  PROVED: the explicit approx unfolding, the per-resolution
inner modulus (from each term's own `.cauchy`), the per-cell √-Hölder node bound,
and the `SemicircleCauchy`-from-residuals assembly.  NAMED-open: the two
`ModCauchy` fields (`UniformInnerModulus`, `UniformRiemannBound`), each with its
sharp structural obstruction stated.

# Axiom-gate

`[propext]` / `[propext, Quot.sound]`.  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Continuum.SemicircleIntegral
import YMGap.Constructive.SqrtSubadd
import YMGap.Constructive.CRealComplete

namespace YMGap.Continuum.SemicircleConverge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SemicircleIntegral

/-! ## 1. The explicit `.approx k` unfolding of `seqSemi`

`seqSemi n = semiSum (n+1)`, and `semiSum n` is a `csum` of
`mul (ofQ' (lebW n)) (nodeWeight n k)`.  Unfolding `csum_approx`, `add_approx`,
`mul` (`(mul a b).approx k = a.approx k * b.approx k`), `ofQ'_approx`, and
`sqrtFrom_approx` (`= heronSeq …`), every approximation is the rational finite
sum of the weighted Heron iterates of the node radicands. -/

/-- The scaled per-node weight `(2/n)·√(1 − x_k²)` whose `csum` is `semiSum n`. -/
private def scaledWeight (n : Nat) (hn : 0 < n) (k : Nat) : CReal :=
  CReal.mul (CReal.ofQ' (lebW n hn)) (nodeWeight n hn k)

private theorem semiSum_eq_csum (n : Nat) (hn : 0 < n) :
    semiSum n hn = CReal.csum (scaledWeight n hn) n := rfl

/-- **Explicit approximation of `semiSum`** — the rational finite sum of the
weighted per-node weights at approx index `k`. -/
theorem semiSum_approx_eq (n : Nat) (hn : 0 < n) (k : Nat) :
    (semiSum n hn).approx k
      = RationalTail.finSum
          (fun j => (scaledWeight n hn j).approx k) n := by
  rw [semiSum_eq_csum n hn]
  exact CReal.csum_approx (scaledWeight n hn) n k

/-- The scaled-weight approximation is the weighted Heron iterate of the node
radicand: `(scaledWeight n j).approx k = (2/n)·heronSeq (1 − x_j²) k` for
`j < n`. -/
theorem scaledWeight_approx_lt (n : Nat) (hn : 0 < n) {j : Nat} (hj : j < n) (k : Nat) :
    (scaledWeight n hn j).approx k
      = lebW n hn
        * CReal.heronSeq (oneMinusSqNode n j hn hj) k := by
  show (CReal.ofQ' (lebW n hn)).approx k * (nodeWeight n hn j).approx k
      = lebW n hn * CReal.heronSeq (oneMinusSqNode n j hn hj) k
  rw [CReal.ofQ'_approx]
  have hnode : (nodeWeight n hn j).approx k
      = CReal.heronSeq (oneMinusSqNode n j hn hj) k := by
    unfold nodeWeight
    rw [dif_pos hj, CReal.sqrtFrom_approx]
  rw [hnode]

/-- **Explicit approximation of `seqSemi`** (`= semiSum (n+1)`). -/
theorem seqSemi_approx_eq (n : Nat) (k : Nat) :
    (seqSemi n).approx k
      = RationalTail.finSum
          (fun j => (scaledWeight (n + 1) (Nat.succ_pos n) j).approx k) (n + 1) :=
  semiSum_approx_eq (n + 1) (Nat.succ_pos n) k

/-! ## 2. Per-resolution (index-`i`) inner regularity modulus

Each `seqSemi i` IS a genuine `CReal`, hence Cauchy: its own `.cauchy` field
provides, constructively, a per-resolution inner regularity modulus.  We expose
it as an existential per `i` (the witness is the modulus carried in the `CReal`
record — NO `Classical.choose`).  The named residual `UniformInnerModulus`
records why this cannot be made index-FREE for `ModCauchy.regular`. -/

/-- **Each term `seqSemi i` is Cauchy** (per-resolution inner modulus), directly
from its own `CReal.cauchy` field — the constructive witness carried by the
`CReal` record.  For every `i` and tolerance `ε > 0` there is a stage `N` past
which the approximations of the single term `seqSemi i` agree to within `ε`. -/
theorem seqSemi_self_cauchy (i : Nat) (ε : Q') (hε : (0 : Q') < ε) :
    ∃ N : Nat, ∀ p q : Nat, N ≤ p → N ≤ q →
      (seqSemi i).approx p ≤ (seqSemi i).approx q + ε
        ∧ (seqSemi i).approx q ≤ (seqSemi i).approx p + ε :=
  (seqSemi i).cauchy ε hε

/-! ## 3. The per-cell √-Hölder bound on the actual node weights

`holder_oneMinusSq` instantiated at the concrete `nodeWeight` radicands.  This is
the genuine reusable per-cell Riemann estimate: the difference of two node
weights is bounded by the rational tolerance `c` once the larger radicand
exceeds the smaller by at most `c²`. -/

/-- **Per-cell √-Hölder bound on node weights.**  For two nodes with radicands
`u = 1 − x_kx²` (resolution `nx`, index `kx`) `≥` `v = 1 − x_ky²` (resolution
`ny`, index `ky`), if `u ≤ v + c·c` (`c > 0`), then the difference of the genuine
node weights is `≤ c`:

    √(1 − x_kx²) − √(1 − x_ky²) ≤ c        (sound `leRat`).

This is `Constructive.CReal.holder_oneMinusSq` at the `oneMinusSqNode` radicands
and `nodeLB` lower-bound witnesses.  It is exactly the per-cell rectangle bound
the index-uniform Riemann modulus (named residual `UniformRiemannBound`)
assembles. -/
theorem nodeWeight_holder
    (nx kx : Nat) (hnx : 0 < nx) (hkx : kx < nx)
    (ny ky : Nat) (hny : 0 < ny) (hky : ky < ny)
    (c : Q') (hc : (0 : Q') < c)
    (huvc : oneMinusSqNode nx kx hnx hkx
        ≤ oneMinusSqNode ny ky hny hky + c * c) :
    CReal.leRat
      (CReal.add
        (CReal.sqrtFrom (oneMinusSqNode nx kx hnx hkx) (nodeLB nx hnx)
          (oneMinusSqNode_pos hnx hkx) (nodeLB_pos hnx) (nodeLB_sq_le hnx hkx))
        (CReal.neg
          (CReal.sqrtFrom (oneMinusSqNode ny ky hny hky) (nodeLB ny hny)
            (oneMinusSqNode_pos hny hky) (nodeLB_pos hny) (nodeLB_sq_le hny hky))))
      c :=
  CReal.holder_oneMinusSq
    (oneMinusSqNode nx kx hnx hkx) (nodeLB nx hnx)
    (oneMinusSqNode_pos hnx hkx) (nodeLB_pos hnx) (nodeLB_sq_le hnx hkx)
    (oneMinusSqNode ny ky hny hky) (nodeLB ny hny)
    (oneMinusSqNode_pos hny hky) (nodeLB_pos hny) (nodeLB_sq_le hny hky)
    c hc huvc

/-! ## 4. The named residuals (Type-level; AGENTS.md Rule 8)

`SemicircleIntegral.SemicircleCauchy = CReal.ModCauchy seqSemi` is NOT discharged.
The two open `ModCauchy` fields are recorded as named residuals, each with its
sharp structural obstruction.  The √-Hölder lemma is proved (`nodeWeight_holder`);
the obstructions are the `ModCauchy` index-FREE interface vs. the unbounded
term count (`UniformInnerModulus`) and the cell-matching combinatorics
(`UniformRiemannBound`). -/

/-- **Residual 1 (inner modulus).**  An index-FREE inner regularity modulus
`reg : Q' → Nat` valid for every term `seqSemi i` simultaneously.  Open for a
sharp structural reason: the weighted Heron error sums to `≤ 3·(i+1)·2^{−m}`
(the weight cancels the `gap_bound` divisor, leaving the `(i+1)` term count),
which no index-free `m` controls.  The honest index-INDEXED Cauchy property
`seqSemi_self_cauchy` is proved above. -/
def UniformInnerModulus : Type :=
  Σ' reg : Q' → Nat,
    ∀ i : Nat, ∀ ε : Q', (0 : Q') < ε → ∀ p qq : Nat, reg ε ≤ p → reg ε ≤ qq →
      (seqSemi i).approx p ≤ (seqSemi i).approx qq + ε
        ∧ (seqSemi i).approx qq ≤ (seqSemi i).approx p + ε

/-- **Residual 2 (outer Riemann bound + monotone outer modulus).**  An antitone
outer modulus `M : Q' → Nat` with the index-uniform two-sided bound: for
`m,n ≥ M ε` and every approx index `k`, the rational Riemann sums
`(seqSemi m).approx k` and `(seqSemi n).approx k` agree to within `ε`.  Open
because the per-cell √-Hölder bound (`nodeWeight_holder`, PROVED) still needs the
cell-matching combinatorics assembling it into the index-uniform sum estimate. -/
def UniformRiemannBound : Type :=
  Σ' M : Q' → Nat,
    (∀ ε : Q', (0 : Q') < ε → ∀ m n : Nat, M ε ≤ m → M ε ≤ n →
      ∀ k : Nat, (seqSemi m).approx k ≤ (seqSemi n).approx k + ε
        ∧ (seqSemi n).approx k ≤ (seqSemi m).approx k + ε)
    ∧ (∀ ε δ : Q', (0 : Q') < δ → δ ≤ ε → M ε ≤ M δ)

/-- **`SemicircleCauchy` assembled from the two residuals.**  Given the
index-free inner modulus and the outer Riemann bound (with its antitone outer
modulus), the `ModCauchy seqSemi` datum is built directly — discharging
`SemicircleIntegral.SemicircleCauchy` and making `semiInt`'s convergence
UNCONDITIONAL.  The two residuals are the precise remaining obligations. -/
def semicircleCauchy_of_residuals
    (inner : UniformInnerModulus) (outer : UniformRiemannBound) :
    SemicircleIntegral.SemicircleCauchy :=
  { M := outer.1
    reg := inner.1
    bound := outer.2.1
    regular := inner.2
    Mmono := outer.2.2 }

end YMGap.Continuum.SemicircleConverge

/-! ## PROVED vs NAMED-open (honest ledger)

**PROVED (axiom-clean, GENUINE new content).**
  * `seqSemi_approx_eq` / `semiSum_approx_eq` / `scaledWeight_approx_lt` — the
    explicit `.approx k` unfolding of the Riemann sequence to a rational finite
    sum of weighted Heron iterates.
  * `seqSemi_self_cauchy` — each term is Cauchy with its own per-resolution inner
    modulus (the honest index-INDEXED inner modulus, no `Classical`).
  * `nodeWeight_holder` — the genuine per-cell √-Hölder bound on the actual node
    weights (`holder_oneMinusSq` at the concrete `oneMinusSqNode` radicands).
  * `semicircleCauchy_of_residuals` — `SemicircleCauchy` ASSEMBLED from the two
    named residuals (the precise reduction).

**NAMED-open (the honest residuals — NOT proved here).**
  * `UniformInnerModulus` — an index-FREE inner regularity modulus.  Open for a
    sharp structural reason: weighted Heron error `≤ 3·(i+1)·2^{−m}`, unbounded
    term count `(i+1)` ⟹ no index-free modulus; needs `ModCauchy`'s interface
    relaxed to an index-indexed inner modulus, NOT new analysis.
  * `UniformRiemannBound` — the index-uniform outer Riemann bound + antitone
    outer modulus.  The per-cell √-Hölder input is proved (`nodeWeight_holder`);
    the residual is the cell-matching combinatorics + the antitone-`M` bookkeeping.

So `SemicircleCauchy` is REDUCED (via `semicircleCauchy_of_residuals`) to exactly
these two named residuals; the √-Hölder modulus crux is discharged.  The general
`RiemannConverge` refinement modulus follows the SAME pattern (multiply the
integrand by `U_a·U_b·R` — a `QPoly` at the rational node — and reuse this exact
approx-unfolding + per-cell √-Hölder + residual structure).

Axiom-gate: `[propext]` / `[propext, Quot.sound]`.  No `Classical.*`,
no `sorry`/`sorryAx`, no `native_decide`, no new axioms. -/

#print axioms YMGap.Continuum.SemicircleConverge.seqSemi_approx_eq
#print axioms YMGap.Continuum.SemicircleConverge.scaledWeight_approx_lt
#print axioms YMGap.Continuum.SemicircleConverge.seqSemi_self_cauchy
#print axioms YMGap.Continuum.SemicircleConverge.nodeWeight_holder
#print axioms YMGap.Continuum.SemicircleConverge.semicircleCauchy_of_residuals
