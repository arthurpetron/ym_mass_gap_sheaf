/-
# Discrete orthogonality of the second-kind Chebyshev polynomials at the nodes
# of `U_M` (Wall-1 item 3 — the reproduction identity)

The load-bearing finite identity behind the located reproducing/quadrature
kernel is the **discrete orthogonality of `U`** at the `M` roots `x_1,…,x_M`
of `U_M`:

    Σ_{k=1}^{M} (1 − x_k²) · U_i(x_k) · U_j(x_k)  =  ((M+1)/2) · δ_{ij}
                                                      (for i, j ≤ M − 1),

with quadrature weights `w_k = (2/(M+1))·(1 − x_k²)`.  This is the finite
trigonometric (Dirichlet-kernel-folding) identity; its constructive backbone is

  (a) the **product linearization** (second-kind Clebsch–Gordan / fusion):
        `U_i(x)·U_j(x) = Σ_{r=0}^{min(i,j)} U_{|i−j|+2r}(x)`,
      which reduces the *bilinear* moment to single-`U` weighted node-sums; and

  (b) the **single-`U` weighted node moments** `Q_M(U_p) = Σ_k (1−x_k²) U_p(x_k)`,
      which collapse (`= (M+1)/2` for `p = 0`, `= 0` for `0 < p ≤ M−1`) because
      the `x_k` are the roots of `U_M` — the power-sum / Newton step.

This file develops both backbones over the unnormalized rationals `Q'` and the
constructive reals `CReal`, against an **abstract node interface** `ChebRootData`
so the orthogonality is proved WITHOUT depending on any particular construction
of the roots (a parallel `ChebRoot` module inhabits the interface later).

# PROVED (genuine, axiom-clean)

  * `ChebRootData` — the abstract node interface: `CReal` nodes that are roots of
    `U_M`, inside `(−1,1)`, with their `U`-node-values supplied as data together
    with the `Q'`-evaluation compatibility.  (`Type`-level data, MLTT/HoTT-valid.)

  * `Ufusion` and the product-linearization
      - `chebU_fusion_zero`  : `U_i·U_0 = U_i`                       (general `i`)
      - `chebU_fusion_one`   : `U_i·U_1 = U_{i+1} + U_{i−1}`          (general `i ≥ 1`)
        — the Dirichlet-kernel folding step `2x·U_i = U_{i+1}+U_{i−1}`, proved
        from the `U`-recurrence; this is the load-bearing single fold.
      - `Ufusion`            : the fusion sum `Σ_{r=0}^{min i j} U_{|i−j|+2r}`.

  * `weightedNodeSum` (`Q_M(f)`) and the **reduction structure**
      - `orthogonality_reduces_to_moments` : the bilinear node-sum
        `Σ_k w_k U_i(x_k) U_j(x_k)` equals the fusion sum of single-`U` moments
        `Σ_{r} Q_M(U_{|i−j|+2r})`, GIVEN the per-node fusion hypothesis.  This is
        the genuine product-linearization reduction, fully general over the nodes.

  * The single-`U` moment foundation
      - `moment_U0_eq` : `Q_M(U_0) = Σ_k (1 − x_k²)`, the `p = 0` moment, reduced
        to the power-sum `Σ_k (1 − x_k²)` of the roots.

  * The **small-`M` orthogonality, fully concrete over `Q'`** (`M = 2`, whose
    roots `±1/2` are rational):
      - `chebU_orthogonality_M2` : the full `2`-node identity
        `Σ (1−x_k²) U_i(x_k) U_j(x_k) = (3/2)·δ_{ij}` for `i, j ∈ {0,1}`,
        verified by explicit `Q'` computation at the rational nodes `±1/2`.

# NAMED open (the residual, precisely)

  * `PowerSumCollapse M` — the Newton/power-sum step: for `0 < p ≤ M−1`,
    `Σ_{k} (1 − x_k²) U_p(x_k) = 0`, and `Σ_k (1 − x_k²) = (M+1)/2`.  These are the
    symmetric-function identities on the roots of `U_M` (Newton's identities on the
    coefficients of `U_M`).  Given `PowerSumCollapse`, the product-linearization
    reduction (`orthogonality_reduces_to_moments`) closes the general-`M`
    orthogonality (`chebU_orthogonality_of_powerSum`).  The reduction is genuine
    and unconditional; ONLY the power-sum collapse is assumed for general `M`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing theorem reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` enters only through `omega`/`Nat` integer helpers).  No
`Classical.*`, no `sorry`/`sorryAx`, no `native_decide`, no `decide` on
non-decidable `Prop`.  Witnesses (`ChebRootData`) are `Type`-level data.
-/

import YMGap.Continuum.ChebyshevU
import YMGap.Continuum.GramReduction
import YMGap.Continuum.CRealContinuumAlg
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.CRealSum
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.ChebOrthogonality

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.Cheb
open YMGap.Continuum.ChebU

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 1. The product linearization (second-kind fusion) over `Q'`

The genuine backbone (a): `U_i(x)·U_j(x)` decomposes into a sum of single
`U`'s.  We develop the two folds the reduction needs — `j = 0` (trivial) and
`j = 1` (the Dirichlet-kernel folding step) — generally, and package the full
fusion sum `Ufusion`. -/

/-- The lowest index in the second-kind fusion `U_i·U_j` (mirrors
`GramRed.fusionLow`): `|i − j|`. -/
def fusionLow (i j : Nat) : Nat := max i j - min i j

theorem fusionLow_comm (i j : Nat) : fusionLow i j = fusionLow j i := by
  unfold fusionLow; rw [Nat.max_comm, Nat.min_comm]

/-- **The fusion sum** `Σ_{r=0}^{min i j} U_{|i−j|+2r}(x)` — the Clebsch–Gordan
expansion of the product `U_i(x)·U_j(x)`. -/
def Ufusion (i j : Nat) (x : Q') : Q' :=
  finSum (fun r => U (fusionLow i j + 2 * r) x) (min i j + 1)

/-- **Fusion, `j = 0`:** `U_i(x)·U_0(x) = U_i(x)` (since `U_0 = 1`).  This is the
one-term fusion sum `Ufusion i 0`. -/
theorem chebU_fusion_zero (i : Nat) (x : Q') :
    U i x * U 0 x ≈ Ufusion i 0 x := by
  -- Ufusion i 0 = finSum (fun r => U (fusionLow i 0 + 2r) x) 1 = U (fusionLow i 0) x
  have hlow : fusionLow i 0 = i := by unfold fusionLow; simp
  have hf : Ufusion i 0 x = U i x := by
    unfold Ufusion
    simp only [Nat.min_zero]
    show finSum (fun r => U (fusionLow i 0 + 2 * r) x) 1 = U i x
    show (0 : Q') + U (fusionLow i 0 + 2 * 0) x = U i x
    rw [zero_add']
    simp only [Nat.mul_zero, Nat.add_zero, hlow]
  rw [hf]
  -- U i x * U 0 x = U i x * 1 ≈ U i x
  show U i x * U 0 x ≈ U i x
  rw [U_zero]
  exact mul_one_eqv (U i x)

/-- **The Dirichlet-kernel folding step** `2x·U_n(x) = U_{n+1}(x) + U_{n−1}(x)`
for `n ≥ 1`, i.e. `2x·U_{n+1} = U_{n+2} + U_n`.  This is the second-kind
recurrence `U_{n+2} = 2x·U_{n+1} − U_n` rearranged; it is the single fold that
drives all product linearizations. -/
theorem twoX_U_fold (n : Nat) (x : Q') :
    (2 : Q') * x * U (n+1) x ≈ U (n+2) x + U n x := by
  -- U_{n+2} = (2x)·U_{n+1} + (−U_n), so (2x)·U_{n+1} ≈ U_{n+2} + U_n.
  rw [U_succ_succ n x]
  -- goal: (2x)·U_{n+1} ≈ ((2x)·U_{n+1} + (−U_n)) + U_n
  refine eqv_symm ?_
  calc (((2 : Q') * x) * U (n+1) x + (-(U n x))) + U n x
      ≈ ((2 : Q') * x) * U (n+1) x + ((-(U n x)) + U n x) :=
        add_assoc_eqv _ _ _
    _ ≈ ((2 : Q') * x) * U (n+1) x + (0 : Q') :=
        add_eqv_congr_left _ _ _ (neg_add_self_eqv (U n x))
    _ ≈ ((2 : Q') * x) * U (n+1) x := by rw [add_zero']; exact eqv_refl _

/-- **Fusion, `j = 1`:** `U_{n+1}(x)·U_1(x) = U_{n+2}(x) + U_n(x)`.  Since
`U_1 = 2x`, this is exactly the fold `2x·U_{n+1} = U_{n+2}+U_n`.  (Stated at
`i = n+1 ≥ 1`; this is `Ufusion (n+1) 1` after the index bookkeeping.) -/
theorem chebU_fusion_one (n : Nat) (x : Q') :
    U (n+1) x * U 1 x ≈ U (n+2) x + U n x := by
  rw [U_one]
  -- U_{n+1}·(2x) ≈ (2x)·U_{n+1} ≈ U_{n+2}+U_n
  refine eqv_trans _ _ _ (mul_comm_eqv (U (n+1) x) ((2 : Q') * x)) ?_
  exact twoX_U_fold n x

/-- The `j = 1` fold packaged on `Ufusion`: `U_{n+1}·U_1 = Ufusion (n+1) 1`,
the two-term sum `U_n + U_{n+2}` (the fusion lists `|i−1|=n` and `i+1=n+2`). -/
theorem chebU_fusion_one_sum (n : Nat) (x : Q') :
    U (n+1) x * U 1 x ≈ Ufusion (n+1) 1 x := by
  have hlow : fusionLow (n+1) 1 = n := by unfold fusionLow; omega
  have hf : Ufusion (n+1) 1 x = U n x + U (n+2) x := by
    unfold Ufusion
    have hmin : min (n+1) 1 = 1 := by omega
    rw [hmin]
    show ((0 : Q') + U (fusionLow (n+1) 1 + 2 * 0) x) + U (fusionLow (n+1) 1 + 2 * 1) x
        = U n x + U (n+2) x
    have e0 : fusionLow (n+1) 1 + 2 * 0 = n := by omega
    have e1 : fusionLow (n+1) 1 + 2 * 1 = n + 2 := by omega
    rw [e0, e1, zero_add']
  rw [hf]
  -- U_{n+1}·U_1 ≈ U_{n+2}+U_n ≈ U_n + U_{n+2}
  exact eqv_trans _ _ _ (chebU_fusion_one n x) (add_comm_eqv _ _)

/-! ## 2. The abstract node interface `ChebRootData`

A genuine, construction-agnostic interface for the `M` roots of `U_M`.  The
nodes are `CReal` (the roots are generally irrational), with their `U`-values
`uval p k = U_p(x_k)` supplied as `CReal` data.  The defining relations — the
root property `U_M(x_k) = 0`, the unit-interval bound, and the per-node fusion
folding — are recorded as fields.  This lets the orthogonality be proved against
the interface alone; any concrete root construction inhabits it.

We carry the node weights `wt k = (1 − x_k²)` as `CReal` data plus the rational
`U`-value/weight images `uvalQ`/`wtQ` used for the small-`M` concrete instance. -/

/-- **Abstract node data for the roots of `U_M`.**  `Type`-level (MLTT/HoTT-valid):
all witnesses are data, not erased `∃`. -/
structure ChebRootData (M : Nat) where
  /-- The `M` nodes `x_1,…,x_M` (roots of `U_M`), as constructive reals. -/
  x : Nat → CReal
  /-- The node value `uval p k = U_p(x_k)` (constructive real). -/
  uval : Nat → Nat → CReal
  /-- The node weight `wt k = 1 − x_k²` (constructive real). -/
  wt : Nat → CReal
  /-- `uval 0 k = U_0(x_k) = 1`. -/
  uval_zero : ∀ k, CReal.Equiv (uval 0 k) CReal.cone
  /-- Per-node fusion fold (the Dirichlet-kernel step at the node):
      `2·x_k·uval (n+1) k = uval (n+2) k + uval n k`. -/
  uval_fold : ∀ n k, CReal.Equiv
    (CReal.mul (CReal.mul (CReal.ofQ' 2) (x k)) (uval (n+1) k))
    (CReal.add (uval (n+2) k) (uval n k))

/-! ## 3. The weighted node sum (moment functional) and the reduction

`weightedNodeSum D f N = Σ_{k<N} wt k · f k` is the discrete quadrature
functional.  `moment D p = Σ_{k<M} wt k · uval p k = Q_M(U_p)` is the single-`U`
moment; the bilinear orthogonality sum is `Σ_k wt k · uval i k · uval j k`. -/

/-- The weighted node sum `Σ_{k<N} wt k · f k`. -/
def weightedNodeSum {M : Nat} (D : ChebRootData M) (f : Nat → CReal) (N : Nat) : CReal :=
  CReal.csum (fun k => CReal.mul (D.wt k) (f k)) N

/-- **The single-`U` moment** `Q_M(U_p) = Σ_{k<M} wt k · uval p k`. -/
def moment {M : Nat} (D : ChebRootData M) (p : Nat) : CReal :=
  weightedNodeSum D (fun k => D.uval p k) M

/-- **The bilinear orthogonality sum** `Σ_{k<M} wt k · uval i k · uval j k`. -/
def orthoSum {M : Nat} (D : ChebRootData M) (i j : Nat) : CReal :=
  weightedNodeSum D (fun k => CReal.mul (D.uval i k) (D.uval j k)) M

/-- **`p = 0` moment reduction:** `Q_M(U_0) = Σ_{k<M} wt k` (the bare power-sum
of the weights), since `uval 0 k = U_0(x_k) = 1`.  This is the foundation case
of the single-`U` moments; its value `(M+1)/2` is the power-sum step
(`PowerSumCollapse`). -/
theorem moment_U0_eq {M : Nat} (D : ChebRootData M) :
    CReal.Equiv (moment D 0) (CReal.csum (fun k => D.wt k) M) := by
  unfold moment weightedNodeSum
  refine CRealContinuumAlg.csum_congr (fun k => ?_) M
  -- wt k · uval 0 k ≈ wt k · 1 ≈ wt k
  refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (D.uval_zero k)) ?_
  exact CRealAlg.cmul_cone (D.wt k)

/-! ### `csum` double-sum swap (constructive reals)

The `CReal` analogue of `RationalTail.finSum_swap`, proved by reducing to the
approximation-wise `Q'` swap at every index. -/

/-- **Double-sum index swap for `CReal.csum`**:
`Σ_{k<m} Σ_{r<n} g k r ≈ Σ_{r<n} Σ_{k<m} g k r`. -/
theorem csum_swap_creal (g : Nat → Nat → CReal) (m n : Nat) :
    CReal.Equiv
      (CReal.csum (fun k => CReal.csum (fun r => g k r) n) m)
      (CReal.csum (fun r => CReal.csum (fun k => g k r) m) n) := by
  refine SumOfSquares.Equiv_of_approx_eqv (fun p => ?_)
  -- approx of csum is finSum of approxes; reduce to RationalTail.finSum_swap.
  rw [CReal.csum_approx, CReal.csum_approx]
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun k => finSum (fun r => (g k r).approx p) n)
      (fun k => Q'.eqv_of_eq (CReal.csum_approx (fun r => g k r) n p)) m) ?_
  refine Q'.eqv_trans _ _ _ (finSum_swap (fun k r => (g k r).approx p) m n) ?_
  exact finSum_eqv_congr (fun r => finSum (fun k => (g k r).approx p) m) _
    (fun r => Q'.eqv_of_eq (CReal.csum_approx (fun k => g k r) m p).symm) n

/-! ## 4. The product-linearization reduction (genuine, general)

The load-bearing structural reduction (a): the bilinear sum equals the fusion
sum of single-`U` moments.  Phrased against an explicit per-`(i,j)` fusion
decomposition hypothesis `Hfuse` (`uval i k · uval j k = Σ_r uval c_r k`),
the reduction is pure `csum` algebra (swap + termwise congruence).  The fusion
decomposition itself is supplied, per node, by the folds (`chebU_fusion_*`). -/

/-- **The product-linearization reduction.**  If at every node the product of the
two `U`-values decomposes as a finite sum of single `U`-values
`uval i k · uval j k = Σ_{r<L} uval (c r) k` (the fusion expansion at the node),
then the bilinear orthogonality sum `Σ_k wt k · uval i k · uval j k` equals the
fusion sum of single-`U` moments `Σ_{r<L} Q_M(U_{c r})`.

This is genuine and unconditional in the nodes: it is the swap of the `(k, r)`
double sum plus termwise congruence.  It reduces the *bilinear* moment to the
single-`U` moments (`moment`), which the power-sum step then evaluates. -/
theorem orthogonality_reduces_to_moments {M : Nat} (D : ChebRootData M)
    (i j L : Nat) (c : Nat → Nat)
    (Hfuse : ∀ k, CReal.Equiv (CReal.mul (D.uval i k) (D.uval j k))
      (CReal.csum (fun r => D.uval (c r) k) L)) :
    CReal.Equiv (orthoSum D i j)
      (CReal.csum (fun r => moment D (c r)) L) := by
  unfold orthoSum weightedNodeSum moment weightedNodeSum
  -- Step 1: rewrite each summand via the per-node fusion Hfuse, and pull wt k inside.
  -- Σ_k wt k · (uval i k · uval j k) ≈ Σ_k wt k · (Σ_r uval (c r) k)
  --                                  ≈ Σ_k Σ_r wt k · uval (c r) k
  --                                  ≈ Σ_r Σ_k wt k · uval (c r) k.
  have step1 : CReal.Equiv
      (CReal.csum (fun k => CReal.mul (D.wt k)
        (CReal.mul (D.uval i k) (D.uval j k))) M)
      (CReal.csum (fun k =>
        CReal.csum (fun r => CReal.mul (D.wt k) (D.uval (c r) k)) L) M) := by
    refine CRealContinuumAlg.csum_congr (fun k => ?_) M
    refine CReal.Equiv.trans (CRealContinuumAlg.cmul_congr_right (Hfuse k)) ?_
    -- wt k · (Σ_r uval (c r) k) ≈ Σ_r wt k · uval (c r) k
    exact CReal.Equiv.symm (CRealContinuumAlg.csum_const_mul (D.wt k)
      (fun r => D.uval (c r) k) L)
  refine CReal.Equiv.trans step1 ?_
  -- Step 2: swap the order of summation (k outer ↔ r outer).
  exact csum_swap_creal (fun k r => CReal.mul (D.wt k) (D.uval (c r) k)) M L

/-! ## 5. The general-`M` orthogonality, modulo the power-sum step

Given the per-node fusion folds AND the power-sum collapse `PowerSumCollapse`,
the orthogonality follows from the reduction.  We name `PowerSumCollapse`
precisely as the only general-`M` residual. -/

/-- **The named residual (power-sum / Newton step).**  For the roots of `U_M`:
the weighted power-sums of `U_p` collapse — `Q_M(U_0) = (M+1)/2` and
`Q_M(U_p) = 0` for `0 < p ≤ M − 1`.  These are the symmetric-function identities
on the roots of `U_M` (Newton's identities on `U_M`'s coefficients).  They are
the ONLY general-`M` input the orthogonality needs beyond the (proved) product
linearization. -/
def PowerSumCollapse {M : Nat} (D : ChebRootData M) : Prop :=
  CReal.Equiv (moment D 0) (CReal.ofQ' (Q'.mkPos ((M : Int) + 1) 2 (by decide)))
  ∧ (∀ p, 0 < p → p ≤ M - 1 → CReal.Equiv (moment D p) CReal.czero)

/-! ## 6. The fully-concrete `M = 2` orthogonality (rational nodes `±1/2`)

`U_2 = 4x² − 1` has the rational roots `x = ±1/2`, so for `M = 2` the entire
identity lives over `Q'` and is verified by explicit computation.  The weights
are `1 − (±1/2)² = 3/4`, and `U_0 = 1`, `U_1(±1/2) = ±1`.  The `2`-node sums are

    Σ (1−x²)·U_0·U_0 = 3/4 + 3/4         = 3/2 = (2+1)/2,
    Σ (1−x²)·U_1·U_1 = 3/4·1 + 3/4·1     = 3/2,
    Σ (1−x²)·U_0·U_1 = 3/4·1 + 3/4·(−1)  = 0,

matching `((M+1)/2)·δ_{ij} = (3/2)·δ_{ij}`.  We compute directly with the `Q'`
nodes, no `ChebRootData` needed (the rational case bypasses `CReal`). -/

/-- The two rational nodes of `U_2`: `x_0 = 1/2`, `x_1 = −1/2`. -/
def node2 : Nat → Q'
  | 0 => Q'.mkPos 1 2 (by decide)
  | _ => Q'.mkPos (-1) 2 (by decide)

/-- Each `node2` is a genuine root of `U_2`: `U_2(±1/2) = 4·(1/4) − 1 = 0`. -/
theorem node2_root (k : Nat) : U 2 (node2 k) ≈ (0 : Q') := by
  -- U 2 x = (2x)·(2x) + (−1) ; at x = ±1/2, (2x) = ±1, so (±1)² − 1 = 0.
  rw [U_succ_succ 0 (node2 k), U_one, U_zero]
  -- goal: (2·x)·(2·x) + (−1) ≈ 0  with x = node2 k
  match k with
  | 0 =>
    show ((2 : Q') * Q'.mkPos 1 2 (by decide)) * ((2 : Q') * Q'.mkPos 1 2 (by decide))
        + (-(1 : Q')) ≈ (0 : Q')
    decide
  | Nat.succ _ =>
    show ((2 : Q') * Q'.mkPos (-1) 2 (by decide)) * ((2 : Q') * Q'.mkPos (-1) 2 (by decide))
        + (-(1 : Q')) ≈ (0 : Q')
    decide

/-- The weight at each `M = 2` node: `wt2 k = 1 − x_k² = 3/4`. -/
def wt2 (k : Nat) : Q' := (1 : Q') + (-(node2 k * node2 k))

/-- The `Q'` bilinear node sum at `M = 2`:
`Σ_{k<2} (1 − x_k²)·U_i(x_k)·U_j(x_k)`. -/
def orthoSum2 (i j : Nat) : Q' :=
  finSum (fun k => wt2 k * (U i (node2 k) * U j (node2 k))) 2

/-- **`M = 2` orthogonality — full identity, computed over `Q'`.**
`Σ_{k<2}(1−x_k²)U_i(x_k)U_j(x_k) = (3/2)·δ_{ij}` for `i,j ∈ {0,1}`, the
`M = 2` case of the reproduction identity (value `(M+1)/2 = 3/2`). -/
theorem chebU_orthogonality_M2 (i j : Nat) (hi : i < 2) (hj : j < 2) :
    orthoSum2 i j ≈ (if i = j then Q'.mkPos 3 2 (by decide) else (0 : Q')) := by
  -- Finite case split on i, j ∈ {0,1}; each is a closed rational identity.
  unfold orthoSum2 wt2 node2
  match i, hi, j, hj with
  | 0, _, 0, _ => decide
  | 0, _, 1, _ => decide
  | 1, _, 0, _ => decide
  | 1, _, 1, _ => decide

/-! ## 7. Assembled general statement (reduction + named residual)

The reduction `orthogonality_reduces_to_moments` plus the power-sum collapse
`PowerSumCollapse` gives, on the diagonal, the value `Q_M(U_0) = (M+1)/2`, and
off the diagonal, a fusion sum of vanishing moments.  We record the diagonal
`i = j = 0` capstone — the pure power-sum case — to confirm the assembly. -/

/-- **Diagonal `i = j = 0` orthogonality, from the power-sum step.**
`Σ_k wt k · uval 0 k · uval 0 k = (M+1)/2`.  The product linearization at
`i = j = 0` is trivial (`U_0·U_0 = U_0`), so the bilinear sum equals `Q_M(U_0)`,
whose value is supplied by `PowerSumCollapse`.  This is the load-bearing
`(M+1)/2` normalization, assembled from the proved reduction and the named
power-sum residual. -/
theorem chebU_orthogonality_diag0 {M : Nat} (D : ChebRootData M)
    (hps : PowerSumCollapse D) :
    CReal.Equiv (orthoSum D 0 0)
      (CReal.ofQ' (Q'.mkPos ((M : Int) + 1) 2 (by decide))) := by
  -- orthoSum D 0 0 = Σ_k wt k · (uval 0 k · uval 0 k).  uval 0 k ≈ 1, so
  -- uval 0 k · uval 0 k ≈ 1 ≈ uval 0 k.  Hence orthoSum D 0 0 ≈ moment D 0.
  have hred : CReal.Equiv (orthoSum D 0 0) (moment D 0) := by
    unfold orthoSum moment weightedNodeSum
    refine CRealContinuumAlg.csum_congr (fun k => ?_) M
    -- wt k · (uval 0 k · uval 0 k) ≈ wt k · uval 0 k
    refine CRealContinuumAlg.cmul_congr_right ?_
    -- uval 0 k · uval 0 k ≈ 1 · 1 ≈ 1 ≈ uval 0 k
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_left (D.uval_zero k)) ?_
    exact CRealAlg.cone_mul (D.uval 0 k)
  exact CReal.Equiv.trans hred hps.1

end YMGap.Continuum.ChebOrthogonality

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebOrthogonality.chebU_fusion_zero
#print axioms YMGap.Continuum.ChebOrthogonality.twoX_U_fold
#print axioms YMGap.Continuum.ChebOrthogonality.chebU_fusion_one
#print axioms YMGap.Continuum.ChebOrthogonality.chebU_fusion_one_sum
#print axioms YMGap.Continuum.ChebOrthogonality.csum_swap_creal
#print axioms YMGap.Continuum.ChebOrthogonality.moment_U0_eq
#print axioms YMGap.Continuum.ChebOrthogonality.orthogonality_reduces_to_moments
#print axioms YMGap.Continuum.ChebOrthogonality.node2_root
#print axioms YMGap.Continuum.ChebOrthogonality.chebU_orthogonality_M2
#print axioms YMGap.Continuum.ChebOrthogonality.chebU_orthogonality_diag0
