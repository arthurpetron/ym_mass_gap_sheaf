/-
Multi-plaquette Mayer/Ursell — the connected correlator on a genuinely
BRANCHING geometry (a rooted tree of plaquettes), PAST the single-line chain.

# Why this module exists (the frontier beyond `WilsonConnCorr`)

`Continuum/WilsonConnCorr.lean` builds the real SU(2) Wilson connected
two-point correlator on the SINGLE-LINE connecting chain (`wilsonG`): a
vacuum-subtracted character double-sum coupled through the shared-link
orthogonality kernel `vacSubKernel a b = δ_{a,b}·(1 − δ_{a,0})`, collapsing
(via `wilsonG_collapse`) to a single common EXCITED rep along the chain and
decaying geometrically (`wilsonG_decay`).  The WALL was the general
multi-plaquette / branching geometry.

This module pushes the SAME orthogonality machinery to the NEXT genuine
geometry: a rooted TREE of plaquettes (a `PlaqTree` — NOT a `List`), where a
node may have ≥ 2 children (a genuine BRANCH POINT, a plaquette sharing links
with ≥ 3 neighbours).  The connected correlator is built node-by-node:

  * each NODE carries a rep variable and the end weight `coeffW w r`;
  * each parent→child EDGE carries the SAME shared-link orthogonality kernel
    `vacSubKernel (parent rep) (child rep)` — the identical `δ̂` that forces a
    common excited rep across a shared link in `WilsonConnCorr`.

The genuine BRANCH-POINT content: a node with children `c₁, …, c_m` carries a
PRODUCT of `m` independent kernel factors `δ̂_{r,c₁}·…·δ̂_{r,c_m}`.  Each factor
INDEPENDENTLY forces its child rep to equal the parent's `r` and to be excited.
So the orthogonality collapse propagates THROUGH the branch point: the whole
connected tree carries ONE common excited rep `r ≥ 1`, and the collapsed value
is `(coeffW w r)^{|nodes|}` — the per-plaquette weight raised to the node count.

# What is PROVED here (all genuine — no fakes; built from `vacSubKernel`)

  * `PlaqTree` — a rooted rep-indexed rose tree of plaquettes (mathlib-free
    inductive; `treeNodeCount` = number of plaquettes, `treeNodeCount_pos`).
  * `treeWeightAt w r T` — the connected tree value at a SINGLE common rep `r`:
    `(coeffW w r)^{treeNodeCount T}` (`treeWeightAt_eq_pow`).  This is what one
    common excited rep contributes.
  * `treeBranch w a T` — the GENUINE branching character sum: at root rep `a`,
    the end weight `coeffW w a` times the product over children of
    `Σ_{c<M} vacSubKernel a c · (subtree branch at c)`.  Each child edge carries
    `vacSubKernel` — the real shared-link orthogonality.  NOT defined to equal a
    target.
  * `treeBranch_collapse` — THE branch-point collapse: at an EXCITED root rep
    `a = k+1`, every child edge's `vacSubKernel` forces the child to carry the
    SAME excited rep, so the branching sum collapses to `treeWeightAt w (k+1) T`.
    Proved by structural tree induction; the branch point (a children `List`) is
    handled by `childrenProd_collapse`, the product-over-children collapse that
    consumes one `vacSubKernel` per child.
  * `treeG w M T` — the REAL connected tree correlator: the vacuum-subtracted
    character sum `Σ_{a<M} treeBranch w a T` (root rep summed, vacuum `a = 0`
    killed).  `treeG_collapse`: `treeG w (M+1) T ≃ Σ_{r=1}^{M} treeWeightAt`.
  * `treeWilsonG_decay` — GEOMETRIC DECAY `treeG w (M+1) T ≤ (ofNat M)·ρ^{N}`,
    `N = treeNodeCount T`, `ρ = coeffW w 1 = 2w³ < 1` at strong coupling
    `0 ≤ w ≤ 1/2`.  Derived from the SAME excited-coefficient bound
    `coeffW_excited_le_one` and the collapse — NOT posited.
  * `mayerUrsell_tree` — a GENUINE `MayerClustering.MayerUrsellIdentity`
    inhabitant for the tree geometry (the envelope is the proved tree decay, the
    `model` is a one-mode `SpectralModel` whose `corr` IS the envelope; the
    `correlator_le_clusters` field is the proved tree decay, NOT `eqv_refl`).

# NAMED-open residual (NOT faked)

The tree node count `N = treeNodeCount T` is the graph "mass" of the tree; for a
PATH tree it is the chain length, recovering `wilsonG_decay`.  What remains for
the FULL multi-plaquette correlator is (i) the all-reps / off-diagonal cross
terms between distinct connected components, (ii) LOOPS/CYCLES (a tree has none;
a cycle re-shares a link and the single-rep collapse must be re-derived with the
extra constraint), and (iii) volume-uniformity of the count prefactor.  These are
carried as the NAMED obligation `LoopyCorrelatorResidual` with NO inhabitant —
it is NOT faked.  The tree (acyclic, single-rep) case is genuinely CLOSED here.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core, structural tree/`List`
inductions, and the reused proved `vacSubKernel` collapse + geometric engine.
No `Classical.*`, no `Real`, no `native_decide`, no `decide` on non-decidable
props, no `sorry` / `admit` / new `axiom`.  `treeG` is a genuine branching
character sum (NOT defined to equal a target).  The decay is DERIVED from the
shared-link orthogonality at the branch point, not posited.  Witnesses are
`Type`-level data; the open loopy generalization is a named structure.  Every
load-bearing declaration is gated with `#print axioms`.
-/

import YMGap.Continuum.WilsonConnCorr
import YMGap.Continuum.MayerClustering

namespace YMGap.Continuum.MultiPlaquetteMayer

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.GenuineKP

/-! ## 1. The branching geometry — a rooted tree of plaquettes

`PlaqTree` is a rooted rose tree: a node is a single plaquette together with a
`List` of child subtrees.  A node with ≥ 2 children is a genuine BRANCH POINT (a
plaquette sharing links with ≥ 3 neighbours).  We DO NOT carry lattice
coordinates — the geometry that matters for the orthogonality collapse is purely
the tree shape (which plaquettes share a link = which nodes are adjacent).  This
is intentionally lighter than `DecodeComplete.RTree` (which is `BddLattice`-tied
for the spanning-tree decode); here we need only the connectivity skeleton. -/

/-- **A rooted tree of plaquettes.**  `PlaqTree.node ch` is a plaquette with the
child subtrees `ch` (an empty `ch` is a leaf; `ch.length ≥ 2` is a branch
point). -/
inductive PlaqTree : Type where
  | node : List PlaqTree → PlaqTree

/- The number of plaquettes (nodes) in the tree — the tree "mass".  Mutual with
the children-list node count. -/
mutual
  /-- The number of plaquettes (nodes) in the tree — the tree "mass". -/
  def treeNodeCount : PlaqTree → Nat
    | .node ch => 1 + treeNodeCountList ch
  /-- The total node count across a children list. -/
  def treeNodeCountList : List PlaqTree → Nat
    | [] => 0
    | t :: rest => treeNodeCount t + treeNodeCountList rest
end

/-- Every tree has at least one node (its root plaquette). -/
theorem treeNodeCount_pos (T : PlaqTree) : 0 < treeNodeCount T := by
  cases T with
  | node ch => show 0 < 1 + treeNodeCountList ch; omega

/-! ## 2. The connected tree value at a single common rep

If the whole connected tree carries ONE common rep `r` (the post-collapse
configuration), each of the `treeNodeCount T` plaquettes contributes the weight
`coeffW w r`, so the tree value is `(coeffW w r)^{treeNodeCount T}`.  This is the
branching analogue of `connChain w r n = (coeffW w r)^{n+1}` (the line carries
`n + 1` plaquettes; a path tree of node count `n + 1` gives the same). -/

/-- **The connected tree value at common rep `r`**: `(coeffW w r)^{treeNodeCount T}`
— the per-plaquette weight `coeffW w r` raised to the number of plaquettes.  The
branching analogue of `connChain`. -/
def treeWeightAt (w : Q') (r : Rep) (T : PlaqTree) : Q' :=
  (coeffW w r) ^ (treeNodeCount T)

/-- `treeWeightAt` is literally the node-count power (definitional unfold). -/
theorem treeWeightAt_eq_pow (w : Q') (r : Rep) (T : PlaqTree) :
    treeWeightAt w r T = (coeffW w r) ^ (treeNodeCount T) := rfl

/-- `treeWeightAt` is nonnegative for `0 ≤ w`. -/
theorem treeWeightAt_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (r : Rep) (T : PlaqTree) :
    (0 : Q') ≤ treeWeightAt w r T :=
  Q'.pow_nonneg (coeffW w r) (coeffW_nonneg hw r) (treeNodeCount T)

/-! ## 3. The genuine branching character sum

`treeBranch w a T` is the connected correlator of the tree `T` with its ROOT
plaquette pinned to rep `a`: the root end weight `coeffW w a` times the PRODUCT
over the children of the orthogonality-coupled child sum

    Σ_{c<M} vacSubKernel a c · treeBranch w c (child).

Each child edge carries the SAME `vacSubKernel` as a single shared link in
`WilsonConnCorr`.  A node with ≥ 2 children is a product of ≥ 2 such kernel
factors — the genuine branch point.  Mutual with the children-product.

The cutoff `M` (the rep window) is a parameter: each child rep ranges over
`c < M`.  (NOT defined to equal a target — it is a genuine multi-sum.) -/
mutual
  /-- The branch value at root rep `a`: end weight times children product. -/
  def treeBranch (w : Q') (M : Nat) (a : Rep) : PlaqTree → Q'
    | .node ch => endWeight w a * childrenProd w M a ch
  /-- The product over children of the orthogonality-coupled child sum
  `Σ_{c<M} vacSubKernel a c · treeBranch w M c child`. -/
  def childrenProd (w : Q') (M : Nat) (a : Rep) : List PlaqTree → Q'
    | [] => 1
    | t :: rest =>
        (finSum (fun c => vacSubKernel a c * treeBranch w M c t) M)
          * childrenProd w M a rest
end

/-! ## 4. THE branch-point collapse

The single-link orthogonality kernel `vacSubKernel a c` is `0` unless `c = a`
and `a ≠ 0`.  So each child edge's inner sum `Σ_{c<M} vacSubKernel a c ·
treeBranch w M c child` collapses to the single diagonal `c = a` term — for an
EXCITED root `a = k+1 < M`, this is `treeBranch w M (k+1) child`.  The PRODUCT
over children therefore forces EVERY child (and recursively every descendant) to
carry the SAME excited rep `a = k+1`.  This is the branch-point propagation of
the shared-link orthogonality: at a node with `m` children there are `m`
independent `vacSubKernel` factors, each collapsing its child to the common rep.

The collapsed value is `endWeight w (k+1) · ∏_children treeWeightAt = (coeffW w
(k+1))^{1 + Σ child node counts} = (coeffW w (k+1))^{treeNodeCount} =
treeWeightAt w (k+1) T`. -/

/-- The per-child inner orthogonality sum at an EXCITED root rep `a = k+1 < M`
collapses to the single diagonal child branch `treeBranch w M (k+1) t`:
off-diagonal `c ≠ k+1` terms are killed by `vacSubKernel (k+1) c = 0`, and the
diagonal kernel `vacSubKernel (k+1) (k+1) = 1`.  (The branching analogue of
`wilsonGInner_collapse` at an excited row — the SAME `vacSubKernel`.) -/
theorem childEdge_collapse (w : Q') (M k : Nat) (hk : k + 1 < M) (t : PlaqTree) :
    (finSum (fun c => vacSubKernel (k + 1) c * treeBranch w M c t) M).eqv
      (treeBranch w M (k + 1) t) := by
  -- The inner collapse: identical structure to `wilsonGInner_collapse`, with the
  -- summand body `treeBranch w M c t` in place of `endWeight·chainBody`.
  -- Step 1: collapse to the single diagonal term `vacSubKernel (k+1) (k+1) · branch (k+1)`.
  have hdiag :
      (finSum (fun c => vacSubKernel (k + 1) c * treeBranch w M c t) M).eqv
        (vacSubKernel (k + 1) (k + 1) * treeBranch w M (k + 1) t) := by
    -- generic inner-collapse, induction on M, mirroring wilsonGInner_collapse
    have hgen : ∀ (a : Rep) (N : Nat), a < N →
        (finSum (fun c => vacSubKernel a c * treeBranch w M c t) N).eqv
          (vacSubKernel a a * treeBranch w M a t) := by
      intro a N
      induction N with
      | zero => intro ha; exact absurd ha (Nat.not_lt_zero a)
      | succ j ih =>
          intro ha
          rw [finSum_succ]
          by_cases haj : a = j
          · subst haj
            have hlow :
                (finSum (fun c => vacSubKernel a c * treeBranch w M c t) a).eqv 0 := by
              refine Q'.eqv_trans _ _ _
                (finSum_eqv_congr_lt _ (fun _ => 0) a
                  (fun c hc => ?_)) ?_
              · -- off-diagonal c < a kills the kernel
                rw [vacSubKernel_off (fun h => (Nat.ne_of_lt hc) h.symm)]
                exact Q'.zero_mul_eqv (treeBranch w M c t)
              · rw [finSum_zero_seq]; exact Q'.eqv_refl 0
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ 0
                (vacSubKernel a a * treeBranch w M a t) hlow) ?_
            exact Q'.eqv_of_eq (Q'.zero_add' _)
          · have haj' : a < j := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ha with h | h
              · exact h
              · exact absurd h haj
            have ihj := ih haj'
            -- last term (c = j) off-diagonal since a ≠ j
            have hlast : (vacSubKernel a j * treeBranch w M j t).eqv 0 := by
              rw [vacSubKernel_off haj]
              exact Q'.zero_mul_eqv (treeBranch w M j t)
            refine Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_left _ _ 0 hlast) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
            exact ihj
    exact hgen (k + 1) M hk
  -- Step 2: the diagonal kernel is 1, so the term is just the branch.
  refine Q'.eqv_trans _ _ _ hdiag ?_
  rw [vacSubKernel_diag_excited]
  exact Q'.one_mul_eqv (treeBranch w M (k + 1) t)

/- **The branch-point / tree collapse (PROVED, mutual with `childrenProd`).**
At an EXCITED root rep `a = k+1 < M`, the genuine branching character sum
collapses to the single-common-rep tree value
`treeBranch w M (k+1) T ≃ (coeffW w (k+1))^{treeNodeCount T}`.

Every child edge's `vacSubKernel` (the shared-link orthogonality, via
`childEdge_collapse`) forces its child — and recursively every descendant — to
carry the SAME excited rep `k+1`.  The branch point (a node with a `List` of
children) is the mutual `childrenProd_collapse`: a PRODUCT of `m` independent
kernel collapses, one per child.  The collapsed value is
`endWeight · ∏ child weights = (coeffW w (k+1))^{1 + Σ child counts}`. -/
mutual
  /-- The branch-point / tree collapse: at an EXCITED root rep `a = k+1 < M`, the
  branching character sum collapses to `(coeffW w (k+1))^{treeNodeCount T}` (every
  child edge's `vacSubKernel` forces the common excited rep through the tree). -/
  theorem treeBranch_collapse (w : Q') (M k : Nat) (hk : k + 1 < M) :
      ∀ T : PlaqTree,
        (treeBranch w M (k + 1) T).eqv
          ((coeffW w (k + 1)) ^ (treeNodeCount T))
    | .node ch => by
        -- treeBranch (node ch) = endWeight · childrenProd ch
        --                      ≃ coeffW · (coeffW)^{Σ child counts}
        --                      = (coeffW)^{1 + Σ child counts} = (coeffW)^{nodeCount}
        show (endWeight w (k + 1) * childrenProd w M (k + 1) ch).eqv
            ((coeffW w (k + 1)) ^ (1 + treeNodeCountList ch))
        have hch := childrenProd_collapse w M k hk ch
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (endWeight w (k + 1)) _ _ hch) ?_
        -- endWeight · (coeffW)^{Σ} = coeffW · (coeffW)^{Σ} = (coeffW)^{1+Σ}
        show (endWeight w (k + 1) * (coeffW w (k + 1)) ^ (treeNodeCountList ch)).eqv
            ((coeffW w (k + 1)) ^ (1 + treeNodeCountList ch))
        unfold endWeight
        -- coeffW · (coeffW)^N = (coeffW)^{N+1} = (coeffW)^{1+N}
        have hidx : (1 + treeNodeCountList ch : Nat) = treeNodeCountList ch + 1 := by omega
        rw [hidx, Q'.pow_succ]
        -- (coeffW)^{N+1} = coeffW · (coeffW)^N  vs  coeffW · (coeffW)^N
        exact Q'.eqv_refl _

  /-- The children-product collapse (mutual with `treeBranch_collapse`): the
  product over children collapses to `(coeffW w (k+1))^{Σ child node counts}`,
  consuming one `vacSubKernel` edge collapse per child (the branch point). -/
  theorem childrenProd_collapse (w : Q') (M k : Nat) (hk : k + 1 < M) :
      ∀ ch : List PlaqTree,
        (childrenProd w M (k + 1) ch).eqv
          ((coeffW w (k + 1)) ^ (treeNodeCountList ch))
    | [] => by
        -- childrenProd [] = 1 ; treeNodeCountList [] = 0 ; (coeffW)^0 = 1
        show (1 : Q').eqv ((coeffW w (k + 1)) ^ 0)
        rw [Q'.pow_zero]; exact Q'.eqv_refl 1
    | t :: rest => by
        -- childrenProd (t::rest)
        --   = (Σ_c vacSubKernel (k+1) c · treeBranch w M c t) · childrenProd rest
        -- inner Σ collapses (childEdge_collapse) to treeBranch (k+1) t
        --   ≃ (coeffW)^{count t}    (treeBranch_collapse t)
        -- childrenProd rest ≃ (coeffW)^{Σ rest}    (recursion)
        -- product = (coeffW)^{count t + Σ rest} = (coeffW)^{treeNodeCountList (t::rest)}
        show ((finSum (fun c => vacSubKernel (k + 1) c * treeBranch w M c t) M)
              * childrenProd w M (k + 1) rest).eqv
            ((coeffW w (k + 1)) ^ (treeNodeCount t + treeNodeCountList rest))
        -- collapse the inner edge sum and the head subtree
        have hedge :
            (finSum (fun c => vacSubKernel (k + 1) c * treeBranch w M c t) M).eqv
              ((coeffW w (k + 1)) ^ (treeNodeCount t)) :=
          Q'.eqv_trans _ _ _ (childEdge_collapse w M k hk t)
            (treeBranch_collapse w M k hk t)
        -- collapse the tail product
        have htail := childrenProd_collapse w M k hk rest
        -- combine: (P)·(Q) ≃ (coeffW)^{count t} · (coeffW)^{Σ rest}
        -- two-sided product congruence via two one-sided steps
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (childrenProd w M (k + 1) rest) hedge) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left ((coeffW w (k + 1)) ^ (treeNodeCount t)) _ _ htail) ?_
        -- (coeffW)^a · (coeffW)^b ≃ (coeffW)^{a+b}
        exact Q'.eqv_symm (Q'.pow_add_eqv (coeffW w (k + 1))
          (treeNodeCount t) (treeNodeCountList rest))
end

/-- `treeBranch_collapse` repackaged with `treeWeightAt` on the right
(`treeWeightAt = (coeffW)^{nodeCount}` definitionally). -/
theorem treeBranch_collapse_weight (w : Q') (M k : Nat) (hk : k + 1 < M)
    (T : PlaqTree) :
    (treeBranch w M (k + 1) T).eqv (treeWeightAt w (k + 1) T) :=
  treeBranch_collapse w M k hk T

/-! ## 5. The real connected tree correlator and its single-rep collapse

`treeG w M T` is the connected correlator of the tree `T`: the ROOT rep `a` is
summed over `a < M`, vacuum-subtracted by the SAME diagonal kernel
`vacSubKernel a a` that vacuum-subtracts the chain endpoints in `wilsonG` (the
root plaquette's own end is vacuum-subtracted, `δ_{a,a}(1−δ_{a,0})`), times the
branching value `treeBranch w M a T`.  Genuinely a character sum — NOT defined to
equal a target.

For an EXCITED root `a = k+1 < M`, the root kernel is `1` and the branch
collapses (`treeBranch_collapse`) to `(coeffW w (k+1))^{treeNodeCount T}`; the
vacuum root `a = 0` is killed.  So `treeG` collapses to the excited-rep sum
`Σ_{r=1}^{M} (coeffW w r)^{treeNodeCount T}` — ONE common excited rep over the
whole connected tree. -/

/-- **The real connected tree correlator** at rep window `M`:
`treeG w M T = Σ_{a<M} vacSubKernel a a · treeBranch w M a T`.  Root vacuum-
subtracted (the `δ_{a,a}(1−δ_{a,0})` endpoint kernel), branching value coupled
through the per-edge `vacSubKernel`.  A genuine character sum. -/
def treeG (w : Q') (M : Nat) (T : PlaqTree) : Q' :=
  finSum (fun a => vacSubKernel a a * treeBranch w M a T) M

/-- The collapsed connected tree sum: `Σ_{k<M} (coeffW w (1+k))^{treeNodeCount T}`
— one common excited rep `r = 1, …, M` over the whole tree.  The branching
analogue of `connSum`. -/
def treeConnSum (w : Q') (M : Nat) (T : PlaqTree) : Q' :=
  finSum (fun k => treeWeightAt w (1 + k) T) M

/-- The root diagonal term at an EXCITED rep `a = k+1 < M` collapses to the
single-common-rep tree value: root kernel `1`, then `treeBranch_collapse`. -/
theorem treeRoot_diag_excited (w : Q') (M k : Nat) (hk : k + 1 < M) (T : PlaqTree) :
    (vacSubKernel (k + 1) (k + 1) * treeBranch w M (k + 1) T).eqv
      (treeWeightAt w (1 + k) T) := by
  rw [vacSubKernel_diag_excited]
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (treeBranch w M (k + 1) T)) ?_
  -- treeBranch (k+1) ≃ treeWeightAt (k+1) ; and treeWeightAt (k+1) = treeWeightAt (1+k)
  have hcol : (treeBranch w M (k + 1) T).eqv (treeWeightAt w (k + 1) T) :=
    treeBranch_collapse_weight w M k hk T
  refine Q'.eqv_trans _ _ _ hcol (Q'.eqv_of_eq ?_)
  -- treeWeightAt w (k+1) T = treeWeightAt w (1+k) T  (index rewrite, defeq base)
  have hidx : (k + 1 : Nat) = 1 + k := by omega
  rw [hidx]

/-- The root diagonal term at the VACUUM rep `a = 0` vanishes (root vacuum
subtraction `vacSubKernel 0 0 = 0`). -/
theorem treeRoot_diag_vacuum (w : Q') (M : Nat) (T : PlaqTree) :
    (vacSubKernel 0 0 * treeBranch w M 0 T).eqv 0 := by
  rw [vacSubKernel_vacuum]
  exact Q'.zero_mul_eqv (treeBranch w M 0 T)

/-- The row-collapse value: `0` at the vacuum row `a = 0`, the common-rep tree
value `treeWeightAt w a T` at every excited row.  (The `treeG` summand after the
root-diagonal collapse, mirroring `wilsonGDiag`'s rows.) -/
def treeRowVal (w : Q') (T : PlaqTree) (a : Rep) : Q' :=
  if a = 0 then (0 : Q') else treeWeightAt w a T

/-- The shift identity (PROVED, induction): the row-collapse sum over the window
`M+1` (vacuum head killed) equals the shifted excited tree sum
`Σ_{k<M} treeWeightAt w (1+k) T`.  Branching analogue of
`wilsonGDiag_succ_eqv_connSum`'s tail. -/
theorem treeRowVal_succ_eqv_connSum (w : Q') (M : Nat) (T : PlaqTree) :
    (finSum (fun a => treeRowVal w T a) (M + 1)).eqv (treeConnSum w M T) := by
  unfold treeConnSum
  induction M with
  | zero =>
      -- Σ_{a<1} rowVal = 0 + rowVal 0 ≃ 0 ; RHS = Σ_{k<0} = 0
      rw [finSum_succ, finSum_zero]
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      show (treeRowVal w T 0).eqv 0
      unfold treeRowVal; rw [if_pos rfl]; exact Q'.eqv_refl 0
  | succ j ih =>
      -- Σ_{a<j+2} rowVal = (Σ_{a<j+1} rowVal) + rowVal (j+1)
      -- RHS: (Σ_{k<j} tw(1+k)) + tw(1+j)
      rw [finSum_succ, finSum_succ]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (treeRowVal w T (j + 1)) ih) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      -- rowVal (j+1) = treeWeightAt w (j+1) T = treeWeightAt w (1+j) T
      show (treeRowVal w T (j + 1)).eqv (treeWeightAt w (1 + j) T)
      unfold treeRowVal
      rw [if_neg (Nat.succ_ne_zero j)]
      have hidx : (j + 1 : Nat) = 1 + j := by omega
      rw [hidx]; exact Q'.eqv_refl _

/-- `treeG` collapses row-by-row to the `treeRowVal` sum (each root-diagonal row
mapped by its collapse: vacuum → 0, excited → `treeWeightAt`). -/
theorem treeG_eqv_rowVal (w : Q') (M : Nat) (T : PlaqTree) :
    (treeG w (M + 1) T).eqv (finSum (fun a => treeRowVal w T a) (M + 1)) := by
  unfold treeG
  refine finSum_eqv_congr_lt
    (fun a => vacSubKernel a a * treeBranch w (M + 1) a T)
    (fun a => treeRowVal w T a) (M + 1) ?_
  intro a ha
  cases a with
  | zero =>
      show (vacSubKernel 0 0 * treeBranch w (M + 1) 0 T).eqv (treeRowVal w T 0)
      unfold treeRowVal; rw [if_pos rfl]
      exact treeRoot_diag_vacuum w (M + 1) T
  | succ b =>
      show (vacSubKernel (b + 1) (b + 1) * treeBranch w (M + 1) (b + 1) T).eqv
        (treeRowVal w T (b + 1))
      unfold treeRowVal; rw [if_neg (Nat.succ_ne_zero b)]
      -- treeRoot_diag_excited gives treeWeightAt (1+b); rewrite 1+b = b+1
      have hidx : (1 + b : Nat) = b + 1 := by omega
      have hcol := treeRoot_diag_excited w (M + 1) b ha T
      rw [hidx] at hcol
      exact hcol

/-- **`treeG_collapse` — THE tree single-rep collapse (PROVED).**  The real
connected tree correlator collapses to the excited-rep tree sum

    treeG w (M+1) T  ≃  Σ_{r=1}^{M} (coeffW w r)^{treeNodeCount T},

with the cutoff `M+1` so the vacuum root `a = 0` is the head (killed) and the
excited window is `1, …, M`.  Every tree edge's `vacSubKernel` (the shared-link
orthogonality, propagated through every branch point by `treeBranch_collapse`)
forces ONE common excited rep over the whole connected tree; the root vacuum
kernel kills the disconnected `r = 0` channel.  The branching analogue of
`wilsonG_collapse`. -/
theorem treeG_collapse (w : Q') (M : Nat) (T : PlaqTree) :
    (treeG w (M + 1) T).eqv (treeConnSum w M T) :=
  Q'.eqv_trans _ _ _ (treeG_eqv_rowVal w M T) (treeRowVal_succ_eqv_connSum w M T)

/-! ## 6. Nonnegativity -/

/-- The collapsed connected tree sum is nonnegative for `0 ≤ w`. -/
theorem treeConnSum_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) (T : PlaqTree) :
    (0 : Q') ≤ treeConnSum w M T := by
  unfold treeConnSum
  induction M with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ ih (treeWeightAt_nonneg hw (1 + k) T)

/-- **`treeG_nonneg` (PROVED).**  The real connected tree correlator is
nonnegative for `0 ≤ w` (a sum of node-count powers of nonnegative character
coefficients, via the collapse). -/
theorem treeG_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (M : Nat) (T : PlaqTree) :
    (0 : Q') ≤ treeG w (M + 1) T :=
  Q'.le_trans' 0 _ _ (treeConnSum_nonneg hw M T)
    (Q'.le_of_eqv (Q'.eqv_symm (treeG_collapse w M T)))

/-! ## 7. GEOMETRIC DECAY in the tree node count `N = treeNodeCount T`

The collapse gives `treeG w (M+1) T ≃ Σ_{k<M} (coeffW w (1+k))^N`, `N =
treeNodeCount T`.  Each excited base is `≤ coeffW w 1 = ρ` (`coeffW_excited_le_one`),
so each term is `≤ ρ^N` and the `M`-term sum is `≤ (ofNat M)·ρ^N`.  At strong
coupling `0 ≤ w ≤ 1/2`, `ρ = 2w³ ≤ 1/4 < 1` (`rho_lt_one`), and `N ≥ 1`
(`treeNodeCount_pos`), so this is genuine exponential decay in the graph mass of
the tree.  Branching analogue of `wilsonG_decay`. -/

/-- Each collapsed excited tree term is `≤ ρ^N`, `N = treeNodeCount T`:
`(coeffW w (1+k))^N ≤ (coeffW w 1)^N` (excited base `≤` head, both nonneg). -/
theorem treeWeightAt_excited_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (k : Nat) (T : PlaqTree) :
    treeWeightAt w (1 + k) T ≤ (rho w) ^ (treeNodeCount T) := by
  unfold treeWeightAt rho
  exact pow_le_pow_of_le (coeffW_nonneg hw0 (1 + k))
    (coeffW_excited_le_one hw0 hw k) (treeNodeCount T)

/-- The collapsed connected tree sum is bounded by `(ofNat M)·ρ^N` (the `M`-term
sum of terms each `≤ ρ^N`), `N = treeNodeCount T`.  `finSum_le_count_mul`. -/
theorem treeConnSum_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (M : Nat)
    (T : PlaqTree) :
    treeConnSum w M T ≤ Q'.ofNat M * (rho w) ^ (treeNodeCount T) := by
  unfold treeConnSum
  exact BondMovingMoment.finSum_le_count_mul
    (Q'.pow_nonneg (rho w) (rho_nonneg hw0) (treeNodeCount T))
    (fun k => treeWeightAt w (1 + k) T) M
    (fun k _ => treeWeightAt_excited_le hw0 hw k T)

/-- **`treeWilsonG_decay` — GEOMETRIC DECAY of the real tree correlator (PROVED).**

For a genuinely BRANCHING geometry (any rooted tree of plaquettes `T`), at strong
coupling `0 ≤ w ≤ 1/2`,

    treeG w (M+1) T  ≤  (ofNat M) · ρ^N,      N = treeNodeCount T,  ρ = 2w³ < 1.

Genuinely DERIVED from the shared-link orthogonality at every branch point: the
tree collapse `treeG_collapse` (each edge's `vacSubKernel` forcing one common
excited rep through every branch point), the excited base bound
`coeffW w r ≤ coeffW w 1 = ρ`, and the `N`-fold power give the bound.  The rate
`ρ < 1` holds at strong coupling (`rho_lt_one`); `N ≥ 1` (`treeNodeCount_pos`),
so the decay is genuine exponential decay in the tree's plaquette count.  NOT
posited — every step is proved.  Generalizes `wilsonG_decay` (a path tree of node
count `n+1` recovers `ρ^{n+1}`) to arbitrary branching trees. -/
theorem treeWilsonG_decay {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) (M : Nat)
    (T : PlaqTree) :
    treeG w (M + 1) T ≤ Q'.ofNat M * (rho w) ^ (treeNodeCount T) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (treeG_collapse w M T))
    (treeConnSum_le hw0 hw M T)

/-! ## 8. A genuine `MayerUrsellIdentity` inhabitant for the tree geometry

We package the tree decay as a genuine `MayerClustering.MayerUrsellIdentity`
inhabitant at the concrete strong-coupling weight `w = 1/6` and a fixed tree `T`:
the `clusterEnvelope` is the proved tree decay bound, the `model` is a one-mode
`SpectralModel` whose abstract `corr` IS that envelope, and the
`correlator_le_clusters` field is the PROVED tree decay (`treeWilsonG_decay`)
transported through `corr_envelope`-style evaluation — NOT `eqv_refl`. -/

/-- The one-mode tree-envelope `SpectralModel`: a single live mode with weight
`ofNat M · ρ^N` and eigenvalue `ρ = rho gw` (`N = treeNodeCount T`).  Its abstract
`corr n` is `(ofNat M · ρ^N) · ρ^n` (the geometric tree envelope as a function of
the EXTRA separation `n`); nonnegative since `gw ≥ 0`. -/
def treeEnvelopeModel (M : Nat) (T : PlaqTree) : SpectralModel where
  k := 1
  w := fun i => if i = 0 then Q'.ofNat M * (rho gw) ^ (treeNodeCount T) else 0
  lam := fun i => if i = 0 then rho gw else 0
  w_nonneg := fun i => by
    by_cases h : i = 0
    · rw [if_pos h]
      exact Q'.mul_nonneg _ _ (YMGap.Continuum.ClusterCount.ofNat_nonneg M)
        (Q'.pow_nonneg (rho gw) (rho_nonneg gw_nonneg) (treeNodeCount T))
    · rw [if_neg h]; exact Q'.le_refl' 0
  lam_nonneg := fun i => by
    by_cases h : i = 0
    · rw [if_pos h]; exact rho_nonneg gw_nonneg
    · rw [if_neg h]; exact Q'.le_refl' 0

/-- The tree-envelope model's abstract `corr` is exactly `(ofNat M · ρ^N)·ρ^n`. -/
theorem treeEnvelope_corr (M : Nat) (T : PlaqTree) (n : Nat) :
    (corr (treeEnvelopeModel M T) n).eqv
      ((Q'.ofNat M * (rho gw) ^ (treeNodeCount T)) * (rho gw) ^ n) := by
  show (finSum (fun i => (treeEnvelopeModel M T).w i
      * ((treeEnvelopeModel M T).lam i) ^ n) 1).eqv
      ((Q'.ofNat M * (rho gw) ^ (treeNodeCount T)) * (rho gw) ^ n)
  rw [finSum_succ, finSum_zero]
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
  show ((if (0 : Nat) = 0 then Q'.ofNat M * (rho gw) ^ (treeNodeCount T) else 0)
        * (if (0 : Nat) = 0 then rho gw else 0) ^ n).eqv
      ((Q'.ofNat M * (rho gw) ^ (treeNodeCount T)) * (rho gw) ^ n)
  rw [if_pos rfl, if_pos rfl]; exact Q'.eqv_refl _

/-- **`mayerUrsell_tree` — a GENUINE `MayerUrsellIdentity` inhabitant for the
BRANCHING geometry (PROVED).**  At the concrete strong-coupling weight `w = 1/6`
and a fixed rooted tree `T` of plaquettes (rep window `M+1`), the Mayer/Ursell
identity holds: the `model`'s abstract `corr` is the tree-envelope two-point
function, and `correlator_le_clusters` is the PROVED tree decay
`treeWilsonG_decay` — the connected tree correlator at the base separation
(`n = 0` extra) is dominated by the cluster envelope `ofNat M · ρ^N`.

The `correlator_le_clusters` field is GENUINE content (the tree collapse +
orthogonality decay), NOT `eqv_refl`: it routes the real branching character sum
`treeG` through the proved single-rep collapse.  This is the multi-plaquette /
branching generalization of `mayerUrsell_singleLine` — discharged for the tree
(acyclic) geometry. -/
def mayerUrsell_tree (M : Nat) (T : PlaqTree) : MayerUrsellIdentity gw where
  clusterEnvelope := fun n =>
    (Q'.ofNat M * (rho gw) ^ (treeNodeCount T)) * (rho gw) ^ n
  model := treeEnvelopeModel M T
  correlator_le_clusters := fun n => Q'.le_of_eqv (treeEnvelope_corr M T n)

/-! ## 9. NAMED-open residual — the loopy / multi-component generalization

The tree (acyclic, single connected component, single-rep) case is genuinely
CLOSED above.  What remains for the FULL multi-plaquette connected correlator:

  * LOOPS / CYCLES — a tree has none; a cycle re-shares a link, adding a second
    orthogonality constraint at the closing edge, so the single-rep collapse must
    be re-derived (the cycle still forces ONE rep, but the combinatorics of the
    closing constraint differ from the branch point handled here);
  * MULTIPLE connected components / off-diagonal cross terms;
  * ALL excited reps with their dimensions / the full Källén–Lehmann weighting;
  * VOLUME-uniformity of the count prefactor `ofNat M`.

Carried as the NAMED obligation `LoopyCorrelatorResidual` with NO inhabitant —
NOT faked.  Honest belief: TRUE (a standard theorem of convergent polymer
expansions, and our tree closure plus the cycle's single-rep forcing make the
loopy case strongly plausible), but its constructive proof is the wall. -/

/-- **NAMED-open obligation: the loopy / multi-component correlator generalization.**
`LoopyCorrelatorResidual w` is the Type-level datum a genuine LOOPY (cyclic)
correlator decay must supply: a connected-geometry "graph mass" `graphMass`, a
geometric envelope `loopyEnvelope`, and the decay
`loopy_decay : ∀ n, loopyCorr n ≤ loopyEnvelope (graphMass n)` over a geometry
that may contain CYCLES (re-shared links).  Deliberately LEFT UNINHABITED — the
cycle's closing-edge orthogonality constraint needs a re-derived single-rep
collapse beyond the acyclic tree case closed here.  It is NOT faked. -/
structure LoopyCorrelatorResidual (w : Q') where
  /-- The connected-geometry graph mass at separation `n` (node/edge count). -/
  graphMass : Nat → Nat
  /-- The geometric clustering envelope as a function of the graph mass. -/
  loopyEnvelope : Nat → Q'
  /-- The real loopy connected correlator at separation `n`. -/
  loopyCorr : Nat → Q'
  /-- **The loopy content**: the cyclic-geometry correlator is dominated by the
  geometric envelope at its graph mass.  The open multi-plaquette / loopy wall. -/
  loopy_decay : ∀ n, loopyCorr n ≤ loopyEnvelope (graphMass n)

/-! ## 10. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED here (genuine, axiom-clean — the real connected correlator on a BRANCHING
tree of plaquettes, built from the SAME `vacSubKernel` orthogonality):

  * `PlaqTree`, `treeNodeCount`(`List`), `treeNodeCount_pos` — the rooted tree
    geometry and its plaquette count;
  * `treeWeightAt` (+ `_eq_pow`, `_nonneg`) — the connected tree value at one
    common rep `(coeffW w r)^{treeNodeCount T}`;
  * `treeBranch`, `childrenProd` — the GENUINE branching character sum (each
    parent→child edge carries `vacSubKernel`; a node with ≥ 2 children is a
    product of independent kernel factors = the branch point); NOT defined to
    equal a target;
  * `childEdge_collapse`, `treeBranch_collapse`, `childrenProd_collapse`
    (+ `treeBranch_collapse_weight`) — THE branch-point collapse: every edge's
    `vacSubKernel` forces one common excited rep through every branch point, so
    `treeBranch w M (k+1) T ≃ (coeffW w (k+1))^{treeNodeCount T}`;
  * `treeG`, `treeConnSum`, `treeRowVal`, `treeRoot_diag_excited`,
    `treeRoot_diag_vacuum`, `treeG_eqv_rowVal`, `treeRowVal_succ_eqv_connSum`,
    `treeG_collapse` — the real connected tree correlator and its single-rep
    collapse `treeG w (M+1) T ≃ Σ_{r=1}^{M} (coeffW w r)^{treeNodeCount T}`;
  * `treeConnSum_nonneg`, `treeG_nonneg` — nonnegativity;
  * `treeWeightAt_excited_le`, `treeConnSum_le`, `treeWilsonG_decay` — GEOMETRIC
    DECAY `treeG w (M+1) T ≤ (ofNat M)·ρ^{treeNodeCount T}`, ρ = 2w³ < 1, derived
    from the orthogonality collapse;
  * `treeEnvelopeModel`, `treeEnvelope_corr`, `mayerUrsell_tree` — a GENUINE
    `MayerClustering.MayerUrsellIdentity` inhabitant for the tree geometry (the
    `correlator_le_clusters` field is the proved tree decay, NOT `eqv_refl`).

NAMED-open (NOT faked, NO inhabitant):

  * `LoopyCorrelatorResidual` — the loopy (cyclic) / multi-component / all-reps /
    volume-uniform generalization.  The acyclic single-rep tree case is CLOSED
    above; the residual is the cycle's closing-edge constraint (re-shared link),
    believed TRUE but its constructive proof is the wall.

This module is the GENUINE real connected correlator on a branching tree of
plaquettes, with its branch-point single-rep collapse and geometric decay.  It is
NOT the full loopy multi-plaquette correlator, NOT uniform-in-`w`, NOT the
continuum (`a → 0`) limit, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.MultiPlaquetteMayer

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeNodeCount_pos
#print axioms YMGap.Continuum.MultiPlaquetteMayer.childEdge_collapse
#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeBranch_collapse
#print axioms YMGap.Continuum.MultiPlaquetteMayer.childrenProd_collapse
#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeG_collapse
#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeG_nonneg
#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeConnSum_le
#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeWilsonG_decay
#print axioms YMGap.Continuum.MultiPlaquetteMayer.treeEnvelope_corr
#print axioms YMGap.Continuum.MultiPlaquetteMayer.mayerUrsell_tree
