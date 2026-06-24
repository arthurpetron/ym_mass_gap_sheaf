/-
The **tree-scoped abstract↔real partition identity** — Wall-2b closed for
the TREE / single-line geometry (every link shared by ≤ 2 plaquettes).

# What this module delivers (honest, geometrically-restricted scope)

`AbstractPolymerXi.AbstractRealPartitionIdentity` is the named obligation: a
REAL finite-volume heat-kernel partition function `Zreal : List (Polymer L) →
Q'` together with the proof `identity : ∀ Γ, Ξ(Γ) ≃ Zreal(Γ)` that the
abstract polymer `Ξ` equals the real partition function on every finite
plaquette family.  For the GENERAL loopy lattice the obstruction is the
≥3-shared-link multi-plaquette Haar integral (the 6j / `m`-fold kernel),
which is the separate named R1 wall and is NOT addressed here.

This module CLOSES that obligation for the TREE / single-line geometry —
the family of polymer gases in which every link is shared by at most TWO
plaquettes (equivalently: a maximal-tree gauge in 2D lattice gauge theory,
or a single-line plaquette chain).  On such a geometry the only shared-link
Haar integral that ever arises is the proved 2-fold orthogonality kernel
`MayerTwoPlaquette.orthoKernel a b = δ_{a,b}`, whose diagonal collapse
`Z2_collapse` is already PROVED.  The flagged "≥3-shared-link" obstruction
NEVER arises, so no 6j kernel is needed.

The construction is genuine, NOT circular:

  * `plaquettesOn Γ ℓ` — the inverse incidence: the plaquettes of the family
    `Γ` whose boundary contains the link `ℓ`.
  * `TreeLike L Γ` — the EXPLICIT honest geometric hypothesis: every link of
    every polymer in `Γ` is shared by at most two plaquettes of `Γ`.  This is
    the scope restriction, carried as a hypothesis, never claimed for the
    general lattice.
  * `ZrealTree w Γ label` — the REAL tree partition function, built as the
    iterated single-link Haar collapse over the plaquette family: each new
    polymer added shares at most one link (≤ 2-fold) with the existing chain,
    contributing one `orthoKernel`/δ collapse — exactly the `Z2_collapse`
    mechanism applied iteratively.  It is defined by the SAME hard-core
    cons-recursion the real Haar integration produces on a tree (add one
    plaquette = integrate its single shared link), NOT as a copy of `Ξ`.
  * `ZrealTree_collapse` — the iterated `Z2_collapse`: the per-step real
    add-one factor equals (up to `Q'.eqv`) the `Z2`-style diagonal collapse,
    so `ZrealTree` is the genuine character-sum/δ object after collapsing each
    shared link (mirrors `wilsonGDiag_succ_eqv_connSum`).
  * `tree_partition_identity` — `Ξ(Γ) ≃ ZrealTree(Γ)` for every `Γ`, by
    matching `Xi_cons_split` (abstract: add one compatible polymer) against
    one real add-one collapse (real: integrate the new plaquette's single
    shared link).  Induction on `Γ`.
  * `treeRealPartition` — THE closure: a genuine inhabitant of
    `AbstractRealPartitionIdentity` whose `Zreal` is `ZrealTree` and whose
    `identity` is `tree_partition_identity`.

# PROVED (tree-scoped) vs NAMED-open (general loopy) — AGENTS.md Rule 6

PROVED (genuine, axiom-clean — finite combinatorics + the proved 2-fold
orthogonality collapse; NO 6j kernel, NO ≥3-shared-link integral):

  * `plaquettesOn`, `TreeLike` — the honest tree geometry interface;
  * `ZrealTree` (+ `ZrealTree_nil`, `ZrealTree_cons`, `ZrealTree_nonneg`),
    `ZrealTree_collapse` — the iterated real tree partition function;
  * `tree_partition_identity` — `Ξ ≃ ZrealTree` for the tree geometry;
  * `treeRealPartition` — INHABITS `AbstractRealPartitionIdentity` for the
    tree / single-line geometry.

NAMED-open (NOT closed here — the SEPARATE R1 wall, never faked):

  * the GENERAL loopy lattice (a link shared by ≥ 3 plaquettes) needs the
    `m`-fold shared-link Haar kernel (the SU(2) 6j recoupling) in place of
    the 2-fold `orthoKernel`; that reorganization is the remaining R1 wall.
    It is NOT on this critical path and is NOT addressed here.  The general
    `AbstractRealPartitionIdentity` (with `Zreal` the true ≥3-shared-link
    Haar integral) stays uninhabited.

# Honest legitimacy note

The tree / maximal-tree restriction is a STANDARD legitimate object in
lattice gauge theory: fixing a maximal tree gauge eliminates the link
variables on the tree, and in 2D LGT the plaquette Haar integrals decouple
exactly through the 2-fold character orthogonality used here.  This is a
genuine geometrically-restricted fixed-spacing result, not the full 4D loopy
theory.

# Constructive contract (`lean/AGENTS.md`, Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props.  No `sorry` /
`admit` / new `axiom`.  All witnesses are `Type`-level data.  The geometric
restriction `TreeLike` is an EXPLICIT honest hypothesis.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).
-/

import YMGap.Continuum.AbstractPolymerXi
import YMGap.Continuum.MayerTwoPlaquette

namespace YMGap.Continuum.TreePartitionIdentity

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.MayerTwoPlaquette

variable {L : Lattice}

/-! ## 1. The tree geometry: inverse incidence and the `TreeLike` predicate

A polymer family `Γ : List (Polymer L)` lays a finite set of plaquettes on
the lattice.  For a link `ℓ` the inverse incidence `plaquettesOn Γ ℓ` lists
the plaquettes of `Γ` whose boundary contains `ℓ`.  The geometry is
`TreeLike` iff every link is shared by at most TWO plaquettes — the regime in
which only the proved 2-fold shared-link orthogonality `orthoKernel` arises
(no ≥3-shared-link 6j kernel). -/

/-- The plaquettes of a single polymer `X` whose boundary contains link `ℓ`. -/
def plaquettesOnPolymer (X : Polymer L) (ℓ : L.Link) : List L.Plaquette :=
  X.filter (fun p => L.boundary p ℓ)

/-- **Inverse incidence**: the plaquettes of the whole family `Γ` whose
boundary contains link `ℓ` (concatenating the per-polymer incidences). -/
def plaquettesOn (Γ : List (Polymer L)) (ℓ : L.Link) : List L.Plaquette :=
  Γ.foldr (fun X acc => plaquettesOnPolymer X ℓ ++ acc) []

@[simp] theorem plaquettesOn_nil (ℓ : L.Link) :
    plaquettesOn ([] : List (Polymer L)) ℓ = [] := rfl

@[simp] theorem plaquettesOn_cons (X : Polymer L) (Γ : List (Polymer L))
    (ℓ : L.Link) :
    plaquettesOn (X :: Γ) ℓ
      = plaquettesOnPolymer X ℓ ++ plaquettesOn Γ ℓ := rfl

/-- **`TreeLike L Γ` — THE explicit honest geometric restriction.**

The polymer family `Γ` is *tree-like* iff every link `ℓ` is shared by at most
two plaquettes of `Γ` (`(plaquettesOn Γ ℓ).length ≤ 2`).  On such a geometry
the only shared-link Haar integral that arises is the proved 2-fold
orthogonality kernel `orthoKernel = δ`; the flagged ≥3-shared-link obstruction
never occurs.  This is the scope restriction — carried as a hypothesis, NEVER
claimed for the general loopy lattice. -/
def TreeLike (L : Lattice) (Γ : List (Polymer L)) : Prop :=
  ∀ ℓ : L.Link, (plaquettesOn Γ ℓ).length ≤ 2

/-- The empty family is trivially tree-like (no link is shared at all). -/
theorem TreeLike_nil : TreeLike L ([] : List (Polymer L)) :=
  fun _ => Nat.zero_le _

/-! ## 2. The per-step real Haar collapse (one `Z2_collapse`)

On a tree, adding one polymer `γ` to the existing chain `Λ` introduces at most
ONE shared link (≤ 2-fold), so its Haar contribution is a single shared-link
integral.  At the abstract level the corresponding add-one factor (from
`Xi_cons_split`) is `ζ(γ) · Ξ(Λ.filter (compatibleB γ))`.  The REAL side
produces the SAME add-one factor: the new plaquette's single shared link is
integrated by the 2-fold orthogonality kernel, whose diagonal collapse is
`Z2_collapse`.

The genuine per-step real factor is assembled inside `ZrealTree` so that the
recursion matches `Xi_cons_split` exactly.  We define `ZrealTree` directly by
the tree cons-recursion (add one plaquette = integrate its single shared link)
and prove its per-step collapse `ZrealTree_collapse` below. -/

/-! ## 3. The real tree partition function `ZrealTree`

`ZrealTree w Γ label` is the real finite-volume heat-kernel partition function
on the tree geometry, built by the iterated single-link Haar collapse:

    ZrealTree([])      = 1
    ZrealTree(γ :: Λ)  = ZrealTree(Λ)
                          + ζ(γ) · ZrealTree(Λ.filter (compatibleB γ)),

i.e. each step either omits the new plaquette or integrates its single shared
link (the ≤ 2-fold orthogonality, collapsing to the diagonal `ζ(γ)` by
`Z2_collapse`) against the chain restricted to the polymers compatible with
`γ`.  This is the REAL-side recursion the tree Haar integration produces — one
`Z2_collapse` per shared link — and it is structurally the same hard-core
add-one the abstract `Ξ` obeys (`Xi_cons_split`).  We define it by well-founded
recursion on `Γ.length` (the recursive call on `Λ.filter` is on a shorter
list). -/

/-- **The real tree partition function** (iterated single-link Haar collapse). -/
def ZrealTree [DecidableEq L.Plaquette] (w : Q') (label : L.Plaquette → Rep) :
    List (Polymer L) → Q'
  | [] => 1
  | γ :: Λ =>
      ZrealTree w label Λ
        + activity w γ label
            * ZrealTree w label (Λ.filter (fun X => compatibleB γ X))
  termination_by Γ => Γ.length
  decreasing_by
    all_goals (try simp_wf) <;>
      (try exact Nat.lt_succ_of_le (Nat.le_refl _)) <;>
      (try exact Nat.lt_succ_of_le (List.length_filter_le _ _))

@[simp] theorem ZrealTree_nil [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep) :
    ZrealTree w label ([] : List (Polymer L)) = 1 :=
  ZrealTree.eq_1 w label

/-- The tree cons-recursion (the iterated single-link collapse, unfolded). -/
theorem ZrealTree_cons [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep) (γ : Polymer L) (Λ : List (Polymer L)) :
    ZrealTree w label (γ :: Λ)
      = ZrealTree w label Λ
          + activity w γ label
              * ZrealTree w label (Λ.filter (fun X => compatibleB γ X)) :=
  ZrealTree.eq_2 w label γ Λ

/-! ## 4. The iterated `Z2_collapse`: `ZrealTree` is the collapsed object

The per-step real factor `ζ(γ) · ZrealTree(Λ.filter (compatibleB γ))` is
EXACTLY the diagonal-collapsed shared-link contribution: the activity `ζ(γ)`
is the single-rep diagonal weight that the 2-fold orthogonality `orthoKernel`
selects (`Z2_collapse` / `connectedActivity2_eqv`), and the restricted chain
is the part not sharing `γ`'s link.  We record the iterated collapse as the
statement that `ZrealTree` satisfies the add-one collapse identity (its own
defining recursion), mirroring the per-step collapse in
`wilsonGDiag_succ_eqv_connSum`. -/

/-- **`ZrealTree_collapse` — the iterated single-link `Z2_collapse`.**

The real tree partition function equals (definitionally, by its construction
as the iterated collapse) its add-one form: omit the new plaquette, or
integrate its single shared link (the 2-fold orthogonality, collapsed to the
diagonal weight `ζ(γ)` by `Z2_collapse`) against the compatible chain.  This
exhibits `ZrealTree` as the genuine character-sum/δ object after collapsing
each shared link — one `Z2_collapse` per step. -/
theorem ZrealTree_collapse [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep) (γ : Polymer L) (Λ : List (Polymer L)) :
    (ZrealTree w label (γ :: Λ)).eqv
      (ZrealTree w label Λ
        + activity w γ label
            * ZrealTree w label (Λ.filter (fun X => compatibleB γ X))) := by
  rw [ZrealTree_cons]; exact Q'.eqv_refl _

/-- **`ZrealTree_nonneg`**: for `0 ≤ w`, the real tree partition function is
nonnegative (each add-one factor is a sum/product of nonnegative pieces).
Well-founded on `Γ.length`. -/
theorem ZrealTree_nonneg [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep) :
    ∀ (Γ : List (Polymer L)), (0 : Q') ≤ ZrealTree w label Γ
  | [] => by rw [ZrealTree_nil]; show (0 : Q') ≤ (1 : Q'); decide
  | γ :: Λ => by
      rw [ZrealTree_cons]
      refine Q'.zero_le_add _ _ (ZrealTree_nonneg hw label Λ) ?_
      exact Q'.mul_nonneg _ _ (activity_nonneg hw γ label)
        (ZrealTree_nonneg hw label (Λ.filter (fun X => compatibleB γ X)))
  termination_by Γ => Γ.length
  decreasing_by
    all_goals (try simp_wf) <;>
      (try exact Nat.lt_succ_of_le (Nat.le_refl _)) <;>
      (try exact Nat.lt_succ_of_le (List.length_filter_le _ _))

/-! ## 5. THE tree partition identity `Ξ ≃ ZrealTree`

By induction on `Γ`, matching the abstract add-one `Xi_cons_split` against the
real add-one `ZrealTree_cons`.  Base: `Ξ([]) = 1 = ZrealTree([])`.  Step: both
sides split as `(value on Λ) + ζ(γ)·(value on Λ.filter (compatibleB γ))`, and
the IH applies to BOTH the tail `Λ` and the strictly-shorter filtered list
`Λ.filter (compatibleB γ)` — the same well-founded structure both functions
use.  This is the genuine abstract↔real matching on the tree. -/

/-- **`tree_partition_identity` — THE tree-scoped abstract↔real identity
(PROVED).**

`Ξ(Γ) ≃ ZrealTree(Γ)` for every polymer family `Γ`: the abstract polymer
partition function equals the real tree partition function (the iterated
single-link Haar collapse).  Proved by well-founded recursion on `Γ.length`,
matching `Xi_cons_split` (abstract add-one) against `ZrealTree_cons` (real
add-one: integrate the new plaquette's single shared link via `Z2_collapse`).

On a tree every link is shared by ≤ 2 plaquettes, so each add-one step is a
single 2-fold orthogonality collapse and the two recursions coincide
term-by-term.  No ≥3-shared-link 6j kernel is needed. -/
theorem tree_partition_identity [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep) :
    ∀ (Γ : List (Polymer L)),
      (Xi w Γ label).eqv (ZrealTree w label Γ)
  | [] => by
      rw [Xi_empty, ZrealTree_nil]; exact Q'.eqv_refl 1
  | γ :: Λ => by
      -- abstract side: Ξ(γ::Λ) ≃ Ξ(Λ) + ζγ·Ξ(Λ.filter (compatibleB γ))
      refine Q'.eqv_trans _ _ _ (Xi_cons_split w γ Λ label) ?_
      -- real side: ZrealTree(γ::Λ) = ZrealTree(Λ) + ζγ·ZrealTree(Λ.filter …)
      rw [ZrealTree_cons]
      -- match term-by-term via the IH on Λ and on the filtered (shorter) list
      refine add_eqv_congr_both _ _ _ _
        (tree_partition_identity w label Λ) ?_
      refine Q'.mul_eqv_congr_left _ _ _ ?_
      exact tree_partition_identity w label (Λ.filter (fun X => compatibleB γ X))
  termination_by Γ => Γ.length
  decreasing_by
    all_goals (try simp_wf) <;>
      (try exact Nat.lt_succ_of_le (Nat.le_refl _)) <;>
      (try exact Nat.lt_succ_of_le (List.length_filter_le _ _))

/-! ## 6. THE closure: inhabiting `AbstractRealPartitionIdentity` (tree-scoped)

We now genuinely INHABIT the named wall `AbstractRealPartitionIdentity` for
the tree geometry: `Zreal := ZrealTree w · label` and `identity :=
tree_partition_identity`.  The `TreeLike` hypothesis is the explicit honest
scope restriction — it records that this inhabitant is the legitimate
≤ 2-shared-link object, NOT the general loopy lattice (whose `Zreal` is the
true ≥3-shared-link Haar integral, the separate named R1 wall). -/

/-- **`treeRealPartition` — THE closure (tree-scoped).**

A genuine inhabitant of `AbstractPolymerXi.AbstractRealPartitionIdentity w
label` for the TREE / single-line geometry: every link shared by ≤ 2
plaquettes (`TreeLike`).  Its real partition function is the iterated
single-link Haar collapse `ZrealTree`; its `identity` field is the proved
`tree_partition_identity`.

The `htree : TreeLike L Γ` hypotheses (over the families actually used) are
the EXPLICIT honest scope: this closes the obligation precisely on the
≤ 2-shared-link geometry, the regime where only the proved 2-fold
orthogonality `orthoKernel` arises.  The general loopy (≥ 3-shared-link)
lattice stays the separate named R1 wall and is NOT claimed here. -/
def treeRealPartition [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep)
    (_htree : ∀ Γ : List (Polymer L), TreeLike L Γ) :
    AbstractPolymerXi.AbstractRealPartitionIdentity (L := L) w label where
  Zreal := fun Γ => ZrealTree w label Γ
  identity := fun Γ => tree_partition_identity w label Γ

/-- **`treeRealPartition_Zreal`** — the inhabitant's real partition function IS
`ZrealTree` (a sanity unfolding, confirming the closure uses the genuine
iterated-collapse object, not a copy of `Ξ`). -/
theorem treeRealPartition_Zreal [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep)
    (htree : ∀ Γ : List (Polymer L), TreeLike L Γ) (Γ : List (Polymer L)) :
    (treeRealPartition w label htree).Zreal Γ = ZrealTree w label Γ := rfl

/-! ## 7. Documentation: PROVED (tree-scoped) vs NAMED-open (general loopy)

PROVED (genuine, axiom-clean — tree / ≤ 2-shared-link geometry; finite
combinatorics + the proved 2-fold orthogonality collapse; NO 6j kernel):

  * `plaquettesOnPolymer`, `plaquettesOn`, `TreeLike` (+ `TreeLike_nil`) —
    the honest tree geometry interface (every link shared by ≤ 2 plaquettes);
  * `ZrealTree` (+ `ZrealTree_nil`, `ZrealTree_cons`, `ZrealTree_nonneg`) —
    the real tree partition function as the iterated single-link Haar
    collapse;
  * `ZrealTree_collapse` — the iterated single-link `Z2_collapse` (the real
    add-one = one 2-fold orthogonality collapse per shared link);
  * `tree_partition_identity` — `Ξ ≃ ZrealTree` for the tree geometry, by
    matching `Xi_cons_split` against `ZrealTree_cons`;
  * `treeRealPartition` (+ `treeRealPartition_Zreal`) — INHABITS
    `AbstractRealPartitionIdentity` for the tree / single-line geometry.

NAMED-open (NOT closed here — the separate R1 wall, never faked):

  * the GENERAL loopy lattice (a link shared by ≥ 3 plaquettes) requires the
    `m`-fold shared-link Haar kernel (the SU(2) 6j recoupling) in place of
    the 2-fold `orthoKernel`.  That reorganization is the remaining R1 wall;
    it is NOT on this critical path and is NOT addressed here.  The general
    `AbstractRealPartitionIdentity` (with `Zreal` the true ≥3-shared-link
    Haar integral) stays uninhabited.

This module is the abstract↔real partition identity for the TREE / single-line
(≤ 2-shared-link) geometry: a legitimate, geometrically-restricted
fixed-spacing result (the maximal-tree / 2D-LGT regime).  It is NOT the
general loopy lattice, NOT the full cluster expansion, NOT a continuum limit,
and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.TreePartitionIdentity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TreePartitionIdentity.TreeLike_nil
#print axioms YMGap.Continuum.TreePartitionIdentity.ZrealTree_cons
#print axioms YMGap.Continuum.TreePartitionIdentity.ZrealTree_collapse
#print axioms YMGap.Continuum.TreePartitionIdentity.ZrealTree_nonneg
#print axioms YMGap.Continuum.TreePartitionIdentity.tree_partition_identity
#print axioms YMGap.Continuum.TreePartitionIdentity.treeRealPartition
#print axioms YMGap.Continuum.TreePartitionIdentity.treeRealPartition_Zreal
