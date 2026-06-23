/-
The **abstract polymer partition function** `Ξ` and the Dobrushin add-one
ratio — the Wall-2 crux on the *abstract-polymer* side, where the gauge
content is ALREADY discharged into opaque nonnegative activities.

# What this module delivers (honest scope)

`Continuum/PolymerModel.lean` supplies the abstract lattice, polymers
(`Polymer L := List Plaquette`), the activity `ζ(X) = ∏_{p∈X} coeffW w
(label p)` with `activity_nonneg`, and the link constraint.
`Continuum/KPCriterion.lean` discharges the GAUGE content of a single
connected polymer (`activity_single_rep`): a constrained connected polymer
carries one common rep, so its activity collapses to a single power.  The
multi-plaquette Haar integral that couples DIFFERENT polymers is therefore
no longer present at this layer — what remains is the PURELY COMBINATORIAL
hard-core polymer gas over `Q'`.

This module builds that gas and proves the Dobrushin / Kotecký–Preiss
add-one bound as a finite induction, with NO Haar integral anywhere:

  * `compatible X Y` — the hard-core (share-no-plaquette) constraint;
    `compatibleB` its `Bool` form; `familyCompatible := List.Pairwise
    compatible` and its `Bool` form `familyCompatibleB` (the filtering
    predicate).
  * `familyActivity w S label = ∏_{X∈S} activity w X label` (a foldr
    product) with `familyActivity_nonneg`.
  * `sublists` — the explicit (Mathlib-free) sub-list enumeration with the
    core cons-split identity `sublists (a::l) = sublists l ++ (sublists l).map
    (a :: ·)` true by `rfl`; mirrors the `ClusterCount` enumeration idiom.
  * `Xi w Γ label` — the abstract polymer partition function
    `Ξ = Σ_{compatible sub-families S ⊆ Γ} ∏_{X∈S} activity X`, with
    `Xi_nonneg` and `Xi_empty : Ξ [] = 1`.
  * `Xi_cons_split` — THE workhorse: `Ξ(γ::Λ) ≃ Ξ(Λ) + activity γ ·
    Ξ(Λ.filter (compatibleB γ))`, the finite `sublists`/`filter`/`foldr`
    bookkeeping (the hard-core inclusion–exclusion add-one identity), proved
    up to `Q'.eqv` as the repo does for such partition-function identities.
  * `Xi_filter_le` — `Ξ(Λ.filter q) ≤ Ξ(Λ)` (filtering drops nonnegative
    summands).
  * `Z_step_ratio` — THE crux (PROVED, finite-combinatorial, NO Haar
    integral): `Ξ(γ::Λ) ≤ Ξ(Λ) · (1 + activity γ)`.  Combines
    `Xi_cons_split` (the `≃`) with `Xi_filter_le` and `activity_nonneg`.
  * `Xi_le_prod_one_plus` — the telescoping `Ξ(Γ) ≤ ∏ (1 + activity γ)`
    (the `logΞ` bound), by `List` induction from `Z_step_ratio`.

# PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (all genuine, finite combinatorics over `Q'`, NO Haar integral):
`familyActivity_nonneg`, `Xi_nonneg`, `Xi_empty`, `Xi_cons_split`,
`Xi_filter_le`, `Z_step_ratio`, `Xi_le_prod_one_plus`.

This is the ABSTRACT polymer `Ξ`: the gauge content is already discharged
by `PolymerModel.activity` / `KPCriterion.activity_single_rep` into the
opaque nonnegative activities, so `Ξ` and the add-one ratio are pure
finite combinatorics.  The connection to the gap chain is documented:
`Ξ ≥ 1` (the empty-family term), so a pinned connected correlator divided
by `Ξ` is bounded by the un-normalized weight; the geometric decay of that
weight is the clustering rate fed to the gap.

NAMED-open (NOT closed here — the separate R1 wall, carried as a Type-level
signature, never faked):

  * `AbstractRealPartitionIdentity` — the identity between this ABSTRACT
    polymer `Ξ` and the REAL finite-volume heat-kernel partition function
    (the ≥3-shared-link multi-plaquette Haar integral).  That Haar
    reorganization is the R1 wall; it is NOT discharged at this layer.

This module is NOT the full cluster expansion, NOT the abstract↔real
identity, NOT a continuum limit, and NOT a 4D Yang–Mills mass gap.  It is
the finite hard-core add-one (Dobrushin) bound on the abstract polymer gas.

# Constructive contract (`lean/AGENTS.md`, Rules 1/6/8)

Mathlib-free; only `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `decide` on non-decidable props.  No `sorry` /
`admit` / new `axiom`.  All witnesses are `Type`-level data.  Every
load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.PolymerModel
import YMGap.Continuum.KPCriterion
import YMGap.Continuum.PolymerPartition
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.AbstractPolymerXi

open YMGap.Constructive
open YMGap.Continuum.PolymerModel

variable {L : Lattice}

/-! ## 0. A small `Q'.eqv` congruence helper -/

/-- Add two `eqv` facts: `a ≃ a'`, `b ≃ b'` ⟹ `a + b ≃ a' + b'`. -/
theorem add_eqv_congr_both (a a' b b' : Q')
    (ha : a.eqv a') (hb : b.eqv b') : (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

/-! ## 1. Hard-core compatibility

Two polymers are *compatible* iff they share no plaquette (the hard-core
exclusion of the polymer gas).  A family of polymers is compatible iff it is
pairwise compatible.  We carry the `Bool` versions `compatibleB` /
`familyCompatibleB` as the actual filtering predicates and the `Prop`
versions `compatible` / `familyCompatible` for the statement of the
hard-core constraint. -/

/-- The hard-core compatibility `Bool` test: `X` and `Y` share no plaquette,
i.e. no element of `X` is a member of `Y`. -/
def compatibleB [DecidableEq L.Plaquette] (X Y : Polymer L) : Bool :=
  X.all (fun p => !(decide (p ∈ Y)))

/-- The hard-core compatibility predicate (`Prop`): `X` and `Y` share no
plaquette. -/
def compatible (X Y : Polymer L) : Prop := ¬ ∃ p, p ∈ X ∧ p ∈ Y

/-- A family of polymers is *compatible* iff it is pairwise compatible. -/
def familyCompatible (S : List (Polymer L)) : Prop :=
  List.Pairwise compatible S

/-- The `Bool` family-compatibility test (the actual `filter` predicate):
the head is compatible with every tail member, and the tail is compatible. -/
def familyCompatibleB [DecidableEq L.Plaquette] : List (Polymer L) → Bool
  | [] => true
  | X :: S => S.all (fun Y => compatibleB X Y) && familyCompatibleB S

@[simp] theorem familyCompatibleB_cons [DecidableEq L.Plaquette]
    (X : Polymer L) (S : List (Polymer L)) :
    familyCompatibleB (X :: S)
      = (S.all (fun Y => compatibleB X Y) && familyCompatibleB S) := rfl

@[simp] theorem familyCompatibleB_nil [DecidableEq L.Plaquette] :
    familyCompatibleB ([] : List (Polymer L)) = true := rfl

/-! ## 2. The family activity (∏ activity over a family) -/

/-- The family activity `∏_{X∈S} ζ(X)`. -/
def familyActivity (w : Q') (S : List (Polymer L))
    (label : L.Plaquette → Rep) : Q' :=
  S.foldr (fun X acc => activity w X label * acc) 1

@[simp] theorem familyActivity_nil (w : Q') (label : L.Plaquette → Rep) :
    familyActivity w ([] : List (Polymer L)) label = 1 := rfl

@[simp] theorem familyActivity_cons (w : Q') (X : Polymer L)
    (S : List (Polymer L)) (label : L.Plaquette → Rep) :
    familyActivity w (X :: S) label
      = activity w X label * familyActivity w S label := rfl

/-- **`familyActivity_nonneg`**: for `0 ≤ w`, the family activity is
nonnegative (a product of nonnegative `activity` factors). -/
theorem familyActivity_nonneg {w : Q'} (hw : (0 : Q') ≤ w)
    (S : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ familyActivity w S label := by
  induction S with
  | nil => show (0 : Q') ≤ (1 : Q'); decide
  | cons X S ih =>
    rw [familyActivity_cons]
    exact Q'.mul_nonneg _ _ (activity_nonneg hw X label) ih

/-! ## 3. The sub-list enumeration (Mathlib-free)

`List.sublists` lives in Mathlib; this substrate is Mathlib-free, so we
define our own `sublists` with the core cons-split identity built in by
construction:

    sublists (a :: l) = sublists l ++ (sublists l).map (a :: ·)

(true by `rfl`).  This mirrors `ClusterCount.choiceSeqs` and is exactly the
split `Xi_cons_split` needs. -/

/-- The explicit list of all sub-lists of a list (the power-set
enumeration). -/
def sublists : List α → List (List α)
  | [] => [[]]
  | a :: l => sublists l ++ (sublists l).map (fun s => a :: s)

@[simp] theorem sublists_nil : sublists ([] : List α) = [[]] := rfl

/-- **The core cons-split identity** (true by `rfl`). -/
@[simp] theorem sublists_cons (a : α) (l : List α) :
    sublists (a :: l) = sublists l ++ (sublists l).map (fun s => a :: s) := rfl

/-- Filtering a `(a :: ·)`-mapped list pulls the filter through the map with
the predicate composed with `(a :: ·)`:

    (l.map (a::·)).filter P = (l.filter (fun S => P (a :: S))).map (a::·).

(`List.filter_map` with the `Function.comp` unfolded by `rfl`.) -/
theorem filter_map_cons {β : Type _} (a : β) (P : List β → Bool)
    (l : List (List β)) :
    (l.map (fun s => a :: s)).filter P
      = (l.filter (fun S => P (a :: S))).map (fun s => a :: s) := by
  rw [List.filter_map]; rfl

/-- Filtering by the constantly-`false` predicate yields the empty list. -/
theorem filter_const_false {β : Type _} (l : List β) :
    l.filter (fun _ => false) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, if_neg (by exact Bool.false_ne_true), ih]

/-! ## 4. The polymer-family sum and its append/map laws -/

/-- The running family-activity sum over a list of families. -/
def polySum (w : Q') (label : L.Plaquette → Rep)
    (Fams : List (List (Polymer L))) : Q' :=
  Fams.foldr (fun S acc => familyActivity w S label + acc) 0

@[simp] theorem polySum_nil (w : Q') (label : L.Plaquette → Rep) :
    polySum w label ([] : List (List (Polymer L))) = 0 := rfl

@[simp] theorem polySum_cons (w : Q') (label : L.Plaquette → Rep)
    (S : List (Polymer L)) (Fams : List (List (Polymer L))) :
    polySum w label (S :: Fams)
      = familyActivity w S label + polySum w label Fams := rfl

/-- `polySum` of any list of families is nonnegative for `0 ≤ w`. -/
theorem polySum_nonneg {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep) (Fams : List (List (Polymer L))) :
    (0 : Q') ≤ polySum w label Fams := by
  induction Fams with
  | nil => exact Q'.le_refl' 0
  | cons S Fams ih =>
    rw [polySum_cons]
    exact Q'.zero_le_add _ _ (familyActivity_nonneg hw S label) ih

/-- **`polySum_append`**: the sum over an append is `Q'.eqv` to the sum of the
two sums. -/
theorem polySum_append (w : Q') (label : L.Plaquette → Rep) :
    ∀ (A B : List (List (Polymer L))),
      (polySum w label (A ++ B)).eqv (polySum w label A + polySum w label B)
  | [], B => by
    show (polySum w label B).eqv (0 + polySum w label B)
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | S :: A, B => by
    show (familyActivity w S label + polySum w label (A ++ B)).eqv
        ((familyActivity w S label + polySum w label A) + polySum w label B)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (polySum_append w label A B)) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv (familyActivity w S label)
        (polySum w label A) (polySum w label B))

/-- **`polySum_map_cons`**: the sum over `(γ :: ·)`-prepended families factors
the head activity out: `Σ ζ(γ::S) = ζ(γ) · Σ ζ(S)` (up to `Q'.eqv`). -/
theorem polySum_map_cons (w : Q') (label : L.Plaquette → Rep) (γ : Polymer L) :
    ∀ (Fams : List (List (Polymer L))),
      (polySum w label (Fams.map (fun s => γ :: s))).eqv
        (activity w γ label * polySum w label Fams)
  | [] => by
    show (0 : Q').eqv (activity w γ label * 0)
    exact Q'.eqv_symm (Q'.mul_zero_eqv (activity w γ label))
  | S :: Fams => by
    show (familyActivity w (γ :: S) label
            + polySum w label (Fams.map (fun s => γ :: s))).eqv
        (activity w γ label * (familyActivity w S label + polySum w label Fams))
    rw [familyActivity_cons]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (polySum_map_cons w label γ Fams)) ?_
    exact Q'.eqv_symm
      (Q'.mul_add_eqv (activity w γ label)
        (familyActivity w S label) (polySum w label Fams))

/-! ## 5. The abstract polymer partition function `Ξ` and its restricted form

`Ξ(Γ) = Σ_{compatible sub-families S ⊆ Γ} ∏_{X∈S} ζ(X)`.

To carry out the hard-core add-one induction cleanly we work with the
`q`-RESTRICTED partition function `XiR q Γ`: the same sum but keeping only
sub-families whose every member satisfies the per-polymer `Bool` predicate
`q` (the running "compatible with the pinned polymer" test).  `Xi` is the
`q = (fun _ => true)` case. -/

/-- The `q`-restricted abstract partition function: sum over compatible
sub-families of `Γ` whose every member satisfies `q`. -/
def XiR [DecidableEq L.Plaquette] (w : Q') (q : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter (fun S => S.all q && familyCompatibleB S))

/-- **The abstract polymer partition function**
`Ξ(w, Γ, label) = Σ_{compatible S ⊆ Γ} ∏_{X∈S} ζ(X)`. -/
def Xi [DecidableEq L.Plaquette] (w : Q') (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) : Q' :=
  polySum w label ((sublists Γ).filter familyCompatibleB)

/-- `Ξ([]) = 1`. -/
@[simp] theorem Xi_empty [DecidableEq L.Plaquette] (w : Q')
    (label : L.Plaquette → Rep) :
    Xi w ([] : List (Polymer L)) label = 1 := rfl

/-- **`Xi_nonneg`**: for `0 ≤ w`, `Ξ ≥ 0`. -/
theorem Xi_nonneg [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ Xi w Γ label :=
  polySum_nonneg hw label _

/-- `XiR q` is nonnegative for `0 ≤ w`. -/
theorem XiR_nonneg [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (q : Polymer L → Bool) (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ XiR w q Γ label :=
  polySum_nonneg hw label _

/-! ## 6. The raw cons-unfolding of `XiR` (pure filter/sublists algebra)

`XiR q (a::Λ) ≃ XiR q Λ + [q a] · ζ(a) · XiR (q && compatibleB a) Λ`,
where `[q a]` is `1` if `q a` and `0` otherwise.  This is the definitional
unfolding via `sublists_cons` + the `filter`/`++`/`map` algebra of §4; NO
induction on the claim, pure algebra.  We split on `q a`. -/

/-- The `all`-of-conjunction law: `S.all q && S.all p = S.all (q && p)`. -/
theorem all_and (q p : Polymer L → Bool) (S : List (Polymer L)) :
    (S.all q && S.all p) = S.all (fun X => q X && p X) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [List.all_cons, ← ih]
    rw [Bool.and_assoc, Bool.and_assoc, ← Bool.and_assoc (S.all q),
      ← Bool.and_assoc (p a)]
    rw [Bool.and_comm (S.all q) (p a)]

/-- **The map-branch of `XiR q (a::Λ)` when `q a = true`.**  The
`(a::·)`-prepended, compatibility+`q`-filtered sub-families of `Λ` sum to
`ζ(a) · XiR (fun X => q X && compatibleB a X) Λ`. -/
theorem XiR_cons_mapbranch_true [DecidableEq L.Plaquette]
    (w : Q') (q : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep) (hqa : q a = true) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => S.all q && familyCompatibleB S))).eqv
    (activity w a label *
      XiR w (fun X => q X && compatibleB a X) Λ label) := by
  -- filter through map, then rewrite the inner predicate to q&&compatibleB form
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => T.all q && familyCompatibleB T) (a :: S))
        = (sublists Λ).filter
            (fun S => S.all (fun X => q X && compatibleB a X)
              && familyCompatibleB S) := by
    apply List.filter_congr
    intro S _hS
    show ((a :: S).all q && familyCompatibleB (a :: S))
        = (S.all (fun X => q X && compatibleB a X) && familyCompatibleB S)
    rw [List.all_cons, hqa, Bool.true_and, familyCompatibleB_cons]
    rw [← Bool.and_assoc, all_and q (fun Y => compatibleB a Y) S]
  rw [hcongr]
  -- now polySum over map(a::)(filter P' (sublists Λ)) = ζ(a) · XiR (...) Λ
  exact polySum_map_cons w label a _

/-- **The map-branch of `XiR q (a::Λ)` when `q a = false`.**  No
`(a::·)`-prepended family survives the `q`-filter, so the branch is `0`. -/
theorem XiR_cons_mapbranch_false [DecidableEq L.Plaquette]
    (q : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (hqa : q a = false) :
    (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => S.all q && familyCompatibleB S)) = [] := by
  rw [filter_map_cons]
  -- composed predicate is always false: (a::S).all q = q a && ... = false
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => T.all q && familyCompatibleB T) (a :: S))
        = (sublists Λ).filter (fun _ => false) := by
    apply List.filter_congr
    intro S _hS
    show ((a :: S).all q && familyCompatibleB (a :: S)) = false
    rw [List.all_cons, hqa, Bool.false_and, Bool.false_and]
  rw [hcongr, filter_const_false, List.map_nil]

/-! ## 7. The fundamental restriction lemma `XiR q Λ ≃ Ξ(Λ.filter q)`

The genuine hard-core bookkeeping: the `q`-restricted partition function of
`Λ` equals the unrestricted partition function of the `q`-FILTERED list
`Λ.filter q`.  Proved by well-founded recursion on `Λ.length` (the recursive
call on `Λ.filter q` is on a shorter list).  This is where the
`filter`/`sublists`/`map` algebra of §4–6 is assembled. -/

/-- **`XiR_eq_Xi_filter` (PROVED).**  `XiR q Λ ≃ Ξ(Λ.filter q)`.  Hard-core
restriction = partition function of the filtered list.  Well-founded on
`Λ.length`. -/
theorem XiR_eq_Xi_filter [DecidableEq L.Plaquette]
    (w : Q') (label : L.Plaquette → Rep) :
    ∀ (q : Polymer L → Bool) (Λ : List (Polymer L)),
      (XiR w q Λ label).eqv (Xi w (Λ.filter q) label)
  | q, [] => by
    -- XiR q [] = polySum (filter P [[]]) ; Λ.filter q = []
    exact Q'.eqv_refl _
  | q, a :: Λ => by
    -- LHS: XiR q (a::Λ) via sublists_cons + filter_append.
    have hLHS :
        (XiR w q (a :: Λ) label).eqv
          (XiR w q Λ label
            + polySum w label
                (((sublists Λ).map (fun s => a :: s)).filter
                  (fun S => S.all q && familyCompatibleB S))) := by
      unfold XiR
      rw [sublists_cons, List.filter_append]
      exact polySum_append w label _ _
    by_cases hqa : q a = true
    · -- a survives: (a::Λ).filter q = a :: Λ.filter q
      have hfa : (a :: Λ).filter q = a :: Λ.filter q := by
        rw [List.filter_cons, if_pos hqa]
      -- RHS: Xi (a :: Λ.filter q) via the SAME algebra (it IS XiR true here):
      -- Xi (a::M) = Xi M + ζ(a) · XiR (compatibleB a) M.
      have hRHS :
          (Xi w (a :: Λ.filter q) label).eqv
            (Xi w (Λ.filter q) label
              + activity w a label
                  * XiR w (fun X => compatibleB a X) (Λ.filter q) label) := by
        unfold Xi
        rw [sublists_cons, List.filter_append]
        refine Q'.eqv_trans _ _ _ (polySum_append w label _ _) ?_
        refine add_eqv_congr_both _ _ _ _ (Q'.eqv_refl _) ?_
        -- map-branch with q' = (fun _ => true): familyCompatibleB only filter
        rw [filter_map_cons]
        have hcongr :
            (sublists (Λ.filter q)).filter
                (fun S => familyCompatibleB (a :: S))
              = (sublists (Λ.filter q)).filter
                  (fun S => S.all (fun X => compatibleB a X)
                    && familyCompatibleB S) := by
          apply List.filter_congr
          intro S _hS
          show familyCompatibleB (a :: S)
              = (S.all (fun X => compatibleB a X) && familyCompatibleB S)
          rw [familyCompatibleB_cons]
        rw [hcongr]
        -- ζ(a)·polySum(filter (compatibleB a-all && fcB) (sublists (Λ.filter q)))
        --  = ζ(a) · XiR (compatibleB a) (Λ.filter q)
        exact polySum_map_cons w label a _
      -- combine: match the two sums term-by-term using IH twice + filter_filter
      refine Q'.eqv_trans _ _ _ hLHS ?_
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (congrArg (fun L => Xi w L label) hfa)) hRHS))
      -- now: XiR q Λ + mapbranch_true  ≃  Xi(Λ.filter q) + ζa · XiR cB (Λ.filter q)
      refine add_eqv_congr_both _ _ _ _ ?_ ?_
      · exact XiR_eq_Xi_filter w label q Λ
      · -- mapbranch_true ≃ ζa · XiR (q&&cB a) Λ ≃ ζa · Xi(Λ.filter (q&&cB a))
        --   = ζa · Xi((Λ.filter q).filter (cB a)) ≃ ζa · XiR (cB a) (Λ.filter q)
        refine Q'.eqv_trans _ _ _
          (XiR_cons_mapbranch_true w q a Λ label hqa) ?_
        refine Q'.mul_eqv_congr_left _ _ _ ?_
        -- XiR (q && cB a) Λ ≃ Xi (Λ.filter (q && cB a))
        refine Q'.eqv_trans _ _ _
          (XiR_eq_Xi_filter w label (fun X => q X && compatibleB a X) Λ) ?_
        -- Xi (Λ.filter (q && cB a)) = Xi ((Λ.filter q).filter (cB a))
        --   ≃ XiR (cB a) (Λ.filter q)   [IH on shorter list Λ.filter q]
        have hff : Λ.filter (fun X => q X && compatibleB a X)
            = (Λ.filter q).filter (fun X => compatibleB a X) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro X _hX
          exact Bool.and_comm (q X) (compatibleB a X)
        rw [hff]
        exact Q'.eqv_symm
          (XiR_eq_Xi_filter w label (fun X => compatibleB a X) (Λ.filter q))
    · -- q a = false: the map-branch vanishes; (a::Λ).filter q = Λ.filter q
      have hqaf : q a = false := by
        cases h : q a with
        | true => exact absurd h hqa
        | false => rfl
      have hfa : (a :: Λ).filter q = Λ.filter q := by
        rw [List.filter_cons, if_neg (by rw [hqaf]; exact Bool.false_ne_true)]
      refine Q'.eqv_trans _ _ _ hLHS ?_
      rw [XiR_cons_mapbranch_false q a Λ hqaf, polySum_nil]
      -- XiR q Λ + 0 ≃ Xi (Λ.filter q) = Xi ((a::Λ).filter q)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) ?_
      rw [hfa]
      exact XiR_eq_Xi_filter w label q Λ
  termination_by _q Λ => Λ.length
  decreasing_by
    all_goals
      first
        | exact Nat.lt_succ_of_le (Nat.le_refl _)
        | exact Nat.lt_succ_of_le (List.length_filter_le _ _)
        | exact Nat.lt_succ_of_le
            (Nat.le_trans (List.length_filter_le _ _) (Nat.le_refl _))

/-! ## 8. THE workhorse `Xi_cons_split` -/

/-- **`Xi_cons_split` — THE workhorse (PROVED, finite combinatorial).**

`Ξ(γ::Λ) ≃ Ξ(Λ) + ζ(γ) · Ξ(Λ.filter (compatibleB γ))` — the hard-core
add-one identity: a sub-family of `γ::Λ` either omits `γ` (contributing
`Ξ(Λ)`) or includes it, in which case the rest must be a compatible
sub-family of `Λ` all-compatible with `γ`, i.e. a sub-family of
`Λ.filter (compatibleB γ)`, weighted by `ζ(γ)`.  Pure `sublists`/`filter`/
`foldr` bookkeeping over `Q'`; NO Haar integral. -/
theorem Xi_cons_split [DecidableEq L.Plaquette] (w : Q') (γ : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (Xi w (γ :: Λ) label).eqv
      (Xi w Λ label
        + activity w γ label * Xi w (Λ.filter (fun X => compatibleB γ X)) label) := by
  -- expand Ξ(γ::Λ) = Ξ(Λ) + map-branch, then identify the map-branch
  have hsplit :
      (Xi w (γ :: Λ) label).eqv
        (Xi w Λ label
          + polySum w label
              (((sublists Λ).map (fun s => γ :: s)).filter familyCompatibleB)) := by
    unfold Xi
    rw [sublists_cons, List.filter_append]
    exact polySum_append w label _ _
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine add_eqv_congr_both _ _ _ _ (Q'.eqv_refl _) ?_
  -- map-branch (q ≡ true) = ζ(γ) · XiR (compatibleB γ) Λ ≃ ζ(γ)·Ξ(Λ.filter cB γ)
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => familyCompatibleB (γ :: S))
        = (sublists Λ).filter
            (fun S => S.all (fun X => compatibleB γ X) && familyCompatibleB S) := by
    apply List.filter_congr
    intro S _hS
    show familyCompatibleB (γ :: S)
        = (S.all (fun X => compatibleB γ X) && familyCompatibleB S)
    rw [familyCompatibleB_cons]
  rw [hcongr]
  refine Q'.eqv_trans _ _ _ (polySum_map_cons w label γ _) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  -- polySum(filter (cB γ-all && fcB)(sublists Λ)) = XiR (cB γ) Λ ≃ Ξ(Λ.filter cB γ)
  exact XiR_eq_Xi_filter w label (fun X => compatibleB γ X) Λ

/-! ## 9. Monotonicity `Xi_filter_le` -/

/-- Helper: if a `Bool` predicate `p₁` implies `p₂` everywhere, then
`polySum (filter p₁ l) ≤ polySum (filter p₂ l)` — the extra summands kept by
the weaker `p₂` are nonnegative.  Proved by induction on `l`. -/
theorem polySum_filter_mono {w : Q'} (hw : (0 : Q') ≤ w)
    (label : L.Plaquette → Rep)
    (p₁ p₂ : List (Polymer L) → Bool)
    (himp : ∀ S, p₁ S = true → p₂ S = true) :
    ∀ (l : List (List (Polymer L))),
      polySum w label (l.filter p₁) ≤ polySum w label (l.filter p₂)
  | [] => Q'.le_refl' 0
  | S :: l => by
    rw [List.filter_cons, List.filter_cons]
    by_cases h1 : p₁ S = true
    · -- p₁ keeps S, hence so does p₂
      have h2 : p₂ S = true := himp S h1
      rw [if_pos h1, if_pos h2, polySum_cons, polySum_cons]
      exact Q'.add_le_add_left _ _ _ (polySum_filter_mono hw label p₁ p₂ himp l)
    · -- p₁ drops S; p₂ may keep or drop it
      have h1f : p₁ S = false := by
        cases hh : p₁ S with
        | true => exact absurd hh h1
        | false => rfl
      rw [if_neg (by rw [h1f]; exact Bool.false_ne_true)]
      by_cases h2 : p₂ S = true
      · rw [if_pos h2, polySum_cons]
        -- polySum (filter p₁ l) ≤ ζS + polySum (filter p₂ l)
        refine Q'.le_trans' _ _ _
          (polySum_filter_mono hw label p₁ p₂ himp l) ?_
        refine Q'.le_trans' _ _ _ ?_
          (Q'.add_le_add_right _ _ _ (Q'.le_refl' _))
        -- polySum(filter p₂ l) ≤ ζS + polySum(filter p₂ l) needs 0 ≤ ζS via comm
        refine Q'.le_trans' _ _ _ ?_
          (Q'.le_of_eqv (Q'.add_comm_eqv (polySum w label (l.filter p₂))
            (familyActivity w S label)))
        exact Q'.add_le_self_of_nonneg _ _ (familyActivity_nonneg hw S label)
      · have h2f : p₂ S = false := by
          cases hh : p₂ S with
          | true => exact absurd hh h2
          | false => rfl
        rw [if_neg (by rw [h2f]; exact Bool.false_ne_true)]
        exact polySum_filter_mono hw label p₁ p₂ himp l

/-- **`Xi_filter_le` (PROVED).**  `Ξ(Λ.filter q) ≤ Ξ(Λ)`: restricting to a
sub-list drops nonnegative summands.  We prove the equivalent
`XiR q Λ ≤ Ξ(Λ)` (sum over a SUBSET of the compatible sub-families) and
transport across `XiR_eq_Xi_filter`. -/
theorem Xi_filter_le [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (q : Polymer L → Bool) (Λ : List (Polymer L)) (label : L.Plaquette → Rep) :
    Xi w (Λ.filter q) label ≤ Xi w Λ label := by
  -- Ξ(Λ.filter q) ≃ XiR q Λ ; need XiR q Λ ≤ Ξ Λ.
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (XiR_eq_Xi_filter w label q Λ)) ?_
  unfold XiR Xi
  -- the q-restricted filter keeps fewer families than the fcB-only filter
  exact polySum_filter_mono hw label
    (fun S => S.all q && familyCompatibleB S)
    (fun S => familyCompatibleB S)
    (fun S hS => by rw [Bool.and_eq_true] at hS; exact hS.2)
    (sublists Λ)

/-! ## 10. THE crux `Z_step_ratio` (the Dobrushin add-one ratio) -/

/-- Algebraic identity `a + b·a ≃ a·(1 + b)` over `Q'` (up to `eqv`). -/
theorem add_mul_one_plus (a b : Q') : (a + b * a).eqv (a * (1 + b)) := by
  -- a·(1+b) ≃ a·1 + a·b ≃ a + a·b ≃ a + b·a
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a 1 b) ?_
  refine add_eqv_congr_both _ _ _ _ (Q'.mul_one_eqv a) (Q'.mul_comm_eqv a b)

/-- **`Z_step_ratio` — THE crux (PROVED, finite-combinatorial, NO Haar
integral).**

`Ξ(γ::Λ) ≤ Ξ(Λ) · (1 + ζ(γ))` — the Dobrushin / Kotecký–Preiss add-one
ratio.  From `Xi_cons_split` (the `≃` add-one identity), the hard-core
monotonicity `Xi_filter_le` (`Ξ(Λ.filter (compatibleB γ)) ≤ Ξ(Λ)`), and
`activity_nonneg` (`0 ≤ ζ(γ)` lets us scale the inequality), then the
algebraic regrouping `Ξ + ζγ·Ξ ≃ Ξ·(1+ζγ)`.

Genuine finite combinatorics over `Q'`; the gauge content is already
discharged into the activities, so NO Haar integral appears.  Base case
`Λ = []` is `Ξ([]) = 1`. -/
theorem Z_step_ratio [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (γ : Polymer L) (Λ : List (Polymer L)) (label : L.Plaquette → Rep) :
    Xi w (γ :: Λ) label
      ≤ Xi w Λ label * (1 + activity w γ label) := by
  -- Ξ(γ::Λ) ≃ Ξ(Λ) + ζγ·Ξ(Λ.filter cBγ) ≤ Ξ(Λ) + ζγ·Ξ(Λ) ≃ Ξ(Λ)·(1+ζγ)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Xi_cons_split w γ Λ label)) ?_
  refine Q'.le_trans' _ _ _ ?_
    (Q'.le_of_eqv (add_mul_one_plus (Xi w Λ label) (activity w γ label)))
  -- Ξ(Λ) + ζγ·Ξ(filter) ≤ Ξ(Λ) + ζγ·Ξ(Λ)
  refine Q'.add_le_add_left _ _ _ ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Xi_filter_le hw (fun X => compatibleB γ X) Λ label)
    (activity_nonneg hw γ label)

/-! ## 11. The telescoping bound `Xi_le_prod_one_plus` (the logΞ bound) -/

/-- The telescoping product `∏_{γ∈Γ} (1 + ζ(γ))`. -/
def prodOnePlus (w : Q') (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    Q' :=
  Γ.foldr (fun γ acc => (1 + activity w γ label) * acc) 1

@[simp] theorem prodOnePlus_nil (w : Q') (label : L.Plaquette → Rep) :
    prodOnePlus w ([] : List (Polymer L)) label = 1 := rfl

@[simp] theorem prodOnePlus_cons (w : Q') (γ : Polymer L)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    prodOnePlus w (γ :: Γ) label
      = (1 + activity w γ label) * prodOnePlus w Γ label := rfl

/-- `1 + ζ(γ) ≥ 0` for `0 ≤ w`. -/
theorem one_plus_activity_nonneg {w : Q'} (hw : (0 : Q') ≤ w)
    (γ : Polymer L) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ 1 + activity w γ label :=
  Q'.zero_le_add _ _ (by decide) (activity_nonneg hw γ label)

/-- `prodOnePlus` is nonnegative. -/
theorem prodOnePlus_nonneg {w : Q'} (hw : (0 : Q') ≤ w)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ prodOnePlus w Γ label := by
  induction Γ with
  | nil => show (0 : Q') ≤ (1 : Q'); decide
  | cons γ Γ ih =>
    rw [prodOnePlus_cons]
    exact Q'.mul_nonneg _ _ (one_plus_activity_nonneg hw γ label) ih

/-- **`Xi_le_prod_one_plus` (PROVED).**  The telescoping `logΞ` bound

    Ξ(Γ) ≤ ∏_{γ∈Γ} (1 + ζ(γ)),

by `List` induction from `Z_step_ratio`: each add-one step multiplies the
bound by `(1 + ζγ)`; the empty case is `Ξ([]) = 1`. -/
theorem Xi_le_prod_one_plus [DecidableEq L.Plaquette] {w : Q'}
    (hw : (0 : Q') ≤ w) (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    Xi w Γ label ≤ prodOnePlus w Γ label := by
  induction Γ with
  | nil =>
    -- Ξ([]) = 1 ≤ 1 = prodOnePlus []
    rw [Xi_empty, prodOnePlus_nil]
    exact Q'.le_refl' 1
  | cons γ Γ ih =>
    rw [prodOnePlus_cons]
    -- Ξ(γ::Γ) ≤ Ξ(Γ)·(1+ζγ) ≤ prodOnePlus Γ · (1+ζγ) = (1+ζγ)·prodOnePlus Γ
    refine Q'.le_trans' _ _ _ (Z_step_ratio hw γ Γ label) ?_
    -- Ξ(Γ)·(1+ζγ) ≤ prodOnePlus Γ · (1+ζγ)  [right-mono, 1+ζγ ≥ 0]
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ih
        (one_plus_activity_nonneg hw γ label)) ?_
    -- prodOnePlus Γ · (1+ζγ) ≃ (1+ζγ) · prodOnePlus Γ
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv (prodOnePlus w Γ label) (1 + activity w γ label))

/-! ## 12. `Ξ ≥ 1` and the doc-wiring to the gap chain

`Ξ ≥ 1` because the empty family `[]` is always a compatible sub-family with
activity `1` (the `s = 0` / vacuum term).  Hence a pinned connected
correlator divided by `Ξ` is bounded by the un-normalized weight:
`⟨W₀;W_n⟩_c ≤ wilsonG / Ξ ≤ wilsonG` (using `Ξ ≥ 1`).  The geometric decay of
`wilsonG` (the real correlator's pinned-cluster weight, ρ = 2w³ in
`WilsonConnCorr.wilsonG_decay`) then supplies the clustering rate fed to
`ClusteringImpliesGap`.  The abstract↔real identity that licenses
`⟨W₀;W_n⟩_c = wilsonG / Ξ` is the SEPARATE R1 wall, named in §13 — it is NOT
discharged here.  We record only the elementary `Ξ ≥ 1` here. -/

/-- **`Xi_ge_one` (PROVED).**  `Ξ(Γ) ≥ 1`: the empty family is always a
compatible sub-family with activity `1`, so it contributes a unit summand;
all other summands are nonnegative.  This is the normalization used to bound
the NORMALIZED correlator `⟨·;·⟩_c = wilsonG / Ξ` by the un-normalized
`wilsonG` in the gap-chain wiring (the abstract↔real identity that produces
that quotient is the named R1 wall of §13). -/
theorem Xi_ge_one [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (1 : Q') ≤ Xi w Γ label := by
  -- sublists Γ always begins with the empty family [] (its first element),
  -- which passes familyCompatibleB; so Ξ = familyActivity [] + (rest) = 1 + rest.
  -- We extract this by case-splitting on the head of the filtered enumeration.
  -- Cleaner: prove polySum (filter fcB (sublists Γ)) ≥ 1 by noting [] ∈ filtered.
  -- The empty family is the LAST element of sublists Γ in our construction;
  -- to avoid positional bookkeeping we induct on Γ.
  induction Γ with
  | nil =>
    -- Ξ([]) = 1
    rw [Xi_empty]; exact Q'.le_refl' 1
  | cons γ Γ ih =>
    -- Ξ(γ::Γ) ≃ Ξ(Γ) + ζγ·Ξ(Γ.filter) ≥ Ξ(Γ) ≥ 1
    refine Q'.le_trans' _ _ _ ih ?_
    refine Q'.le_trans' _ _ _ ?_
      (Q'.ge_of_eqv (Xi_cons_split w γ Γ label))
    -- Ξ(Γ) ≤ Ξ(Γ) + ζγ·Ξ(Γ.filter)
    exact Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (activity_nonneg hw γ label)
        (Xi_nonneg hw _ label))

/-! ## 13. NAMED-open: the abstract↔real partition identity (the R1 wall) -/

/-- **NAMED-open obligation (the R1 wall): the abstract↔real partition
identity.**

`AbstractRealPartitionIdentity` is the Type-level datum a genuine cluster
expansion must supply for a lattice `L` at weight `w`: a REAL finite-volume
heat-kernel partition function `Zreal` (the multi-plaquette Haar integral,
including the ≥3-shared-link couplings) and the proof `identity` that, on
every finite plaquette set, the abstract polymer `Ξ` (built here from the
already-gauge-discharged activities) equals `Zreal` up to `Q'.eqv`.

This structure is deliberately LEFT UNINHABITED: the ≥3-shared-link Haar
reorganization is exactly the remaining R1 wall, NOT discharged by the
finite combinatorics of this module (which handles only the abstract
hard-core gas).  `Xi_cons_split` / `Z_step_ratio` / `Xi_le_prod_one_plus`
above are the abstract-side content; this is the missing abstract↔real
bridge, carried as an obligation, never faked. -/
structure AbstractRealPartitionIdentity [DecidableEq L.Plaquette]
    (w : Q') (label : L.Plaquette → Rep) where
  /-- The real finite-volume heat-kernel partition function over the plaquette
  list `Γ` (the multi-plaquette Haar integral, ≥3-shared-link couplings
  included). -/
  Zreal : List (Polymer L) → Q'
  /-- The abstract↔real identity: the abstract polymer `Ξ` equals the real
  partition function (up to `Q'.eqv`).  THE R1 wall — left uninhabited. -/
  identity : ∀ Γ, (Xi w Γ label).eqv (Zreal Γ)

/-! ## 14. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — finite combinatorics over `Q'`, NO Haar
integral; the gauge content is already discharged into the activities):

  * `compatible` / `compatibleB` / `familyCompatible` / `familyCompatibleB` —
    the hard-core exclusion and its filtering predicate;
  * `familyActivity` (+ `familyActivity_nonneg`) — `∏ activity`;
  * `sublists` (+ `sublists_cons`) — the Mathlib-free sub-family enumeration;
  * `polySum` (+ `polySum_append`, `polySum_map_cons`, `polySum_nonneg`,
    `polySum_filter_mono`) — the family-sum algebra;
  * `Xi` (+ `Xi_empty`, `Xi_nonneg`, `Xi_ge_one`) and the restricted
    `XiR` (+ `XiR_eq_Xi_filter`, the fundamental restriction lemma);
  * `Xi_cons_split` — THE hard-core add-one identity
    `Ξ(γ::Λ) ≃ Ξ(Λ) + ζγ·Ξ(Λ.filter (compatibleB γ))`;
  * `Xi_filter_le` — `Ξ(Λ.filter q) ≤ Ξ(Λ)`;
  * `Z_step_ratio` — THE crux `Ξ(γ::Λ) ≤ Ξ(Λ)·(1+ζγ)` (Dobrushin add-one);
  * `Xi_le_prod_one_plus` — the telescoping `Ξ(Γ) ≤ ∏(1+ζγ)` (logΞ bound).

NAMED-open (NOT faked, NO inhabitant):

  * `AbstractRealPartitionIdentity` — the abstract↔real partition-function
    identity (the ≥3-shared-link multi-plaquette Haar reorganization), the
    separate remaining R1 wall.

This module is NOT the full cluster expansion, NOT the abstract↔real
identity, NOT a continuum limit, and NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.AbstractPolymerXi

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AbstractPolymerXi.familyActivity_nonneg
#print axioms YMGap.Continuum.AbstractPolymerXi.polySum_append
#print axioms YMGap.Continuum.AbstractPolymerXi.polySum_map_cons
#print axioms YMGap.Continuum.AbstractPolymerXi.XiR_eq_Xi_filter
#print axioms YMGap.Continuum.AbstractPolymerXi.Xi_nonneg
#print axioms YMGap.Continuum.AbstractPolymerXi.Xi_empty
#print axioms YMGap.Continuum.AbstractPolymerXi.Xi_cons_split
#print axioms YMGap.Continuum.AbstractPolymerXi.Xi_filter_le
#print axioms YMGap.Continuum.AbstractPolymerXi.Z_step_ratio
#print axioms YMGap.Continuum.AbstractPolymerXi.Xi_le_prod_one_plus
#print axioms YMGap.Continuum.AbstractPolymerXi.Xi_ge_one
