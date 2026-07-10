/-
`XiSignLayer` — Milestone 13.1, D1-loopy step 6: THE TWO-POINT MAYER IDENTITY
IN SUBTRACTION-FREE FORM — the Ursell-sign layer opened.

# The identity

For the hard-core polymer gas, partition the compatible `qP`-families of `Γ`
into FOUR CELLS by (contains a `b₁`-marked member?, contains a `b₂`-marked
member?).  Writing `Ξ := XiR qP`, `XiB(b)` the marked sums, `Av(b)` the
AVOIDANCE sums (no member marked), and `A₁₂ := Av(b₁ ∧ occurring-nowhere b₂)`
the double-avoidance cell, the truncated two-point correlator

    T·Ξ² = XiB2·Ξ − XiB(b₁)·XiB(b₂)      (the Ursell-signed object)

is EXACTLY captured, with no subtraction anywhere, by (`two_point_mayer`):

    XiB2·Ξ + Av(b₁)·Av(b₂)  ≃  XiB(b₁)·XiB(b₂) + A₁₂·Ξ.

Every term is a nonnegative product of partition sums.  This converts the
SIGN layer of the two-point Mayer expansion into an EXACT identity between
manifestly-positive quantities: the correlator's positive (chain) excess is
`A₁₂·Ξ − Av(b₁)·Av(b₂)`, the avoidance-correlation defect.

Corollary (`XiB2_mul_le`): `XiB2·Ξ ≤ XiB(b₁)·XiB(b₂) + A₁₂·Ξ` — the raw
truncated numerator is dominated by the product term plus the double-
avoidance term.

# How it is proved (the constructive route)

  * `polySum_filter_partition` — the binary partition of any filtered
    `polySum` by a second `Bool` test (finite induction, no signs);
  * six aggregation identities assembling `Ξ`, `XiB(bᵢ)`, `Av(bᵢ)` from the
    four cells (partition + `filter_congr` Boolean-shape normalizations);
  * `cell_expand` — the 4-variable degree-2 polynomial identity
    `B(B+D+E+A) + (E+A)(D+A) = (B+D)(B+E) + A(B+D+E+A)`, proved by the
    REFLECTIVE RING NORMALISER (`poly_identity_of_normal_eq`, kernel
    `decide` on canonical normal forms) — the normaliser's intended payload;
  * congruence chaining.

# What remains open (AGENTS.md Rule 6)

The identity is exact; the OPEN analytic content is now isolated in one
inequality: the avoidance-correlation bound `A₁₂·Ξ ≤ Av(b₁)·Av(b₂) +
(connecting-chain sum)·Ξ`-form — i.e. how much double-avoidance exceeds the
product of single avoidances, which is precisely the connected-chain
(genuinely-Ursell) content.  NOT closed here.  No frontier type is touched;
the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.XiChainBound
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.XiSignLayer

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPinnedBridge
open YMGap.Continuum.XiChainBound
open YMGap.Continuum.RingNormaliser

variable {L : Lattice}

/-! ## 1. The binary partition of a filtered `polySum` -/

/-- **`polySum_filter_partition` (PROVED).**  Any filtered `polySum` splits by
a second `Bool` test: `Σ_{P} = Σ_{P ∧ c} + Σ_{P ∧ ¬c}`. -/
theorem polySum_filter_partition {w : Q'} (label : L.Plaquette → Rep)
    (P c : List (Polymer L) → Bool) :
    ∀ (l : List (List (Polymer L))),
      (polySum w label (l.filter P)).eqv
        (polySum w label (l.filter (fun S => P S && c S))
          + polySum w label (l.filter (fun S => P S && !(c S))))
  | [] => by
      show (0 : Q').eqv ((0 : Q') + 0)
      decide
  | S :: l => by
      have ih := polySum_filter_partition (w := w) label P c l
      rw [List.filter_cons, List.filter_cons, List.filter_cons]
      cases hP : P S with
      | false =>
          rw [if_neg (fun h : (false : Bool) = true => Bool.false_ne_true h),
            if_neg (fun h : (false && c S) = true => Bool.false_ne_true h),
            if_neg (fun h : (false && !(c S)) = true => Bool.false_ne_true h)]
          exact ih
      | true =>
          cases hc : c S with
          | true =>
              rw [if_pos (rfl : (true : Bool) = true),
                if_pos (show (true && true) = true from rfl),
                if_neg (fun h : (true && !true) = true => Bool.false_ne_true h),
                polySum_cons, polySum_cons]
              refine Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left _ _ _ ih) ?_
              exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
          | false =>
              rw [if_pos (rfl : (true : Bool) = true),
                if_neg (fun h : (true && false) = true => Bool.false_ne_true h),
                if_pos (show (true && !false) = true from rfl),
                polySum_cons, polySum_cons]
              refine Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left _ _ _ ih) ?_
              -- ζ + (Y + Z) ≃ Y + (ζ + Z)
              refine Q'.eqv_trans _ _ _
                (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
              refine Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
              exact Q'.add_assoc_eqv _ _ _

/-! ## 2. The avoidance sums and the four cells -/

/-- The `b`-AVOIDANCE partition sum: compatible `qP`-families NONE of whose
members is `b`-marked. -/
def XiAvoid [DecidableEq L.Plaquette] (w : Q') (qP b : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter
      (fun S => (S.all qP && familyCompatibleB S) && !(S.any b)))

/-- Cell (marked b₁, unmarked b₂). -/
def cellD [DecidableEq L.Plaquette] (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter
      (fun S => ((S.all qP && familyCompatibleB S) && S.any b1) && !(S.any b2)))

/-- Cell (unmarked b₁, marked b₂). -/
def cellE [DecidableEq L.Plaquette] (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter
      (fun S => ((S.all qP && familyCompatibleB S) && !(S.any b1)) && S.any b2))

/-- Cell (unmarked, unmarked): the DOUBLE-AVOIDANCE sum `A₁₂`. -/
def cellA [DecidableEq L.Plaquette] (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter
      (fun S => ((S.all qP && familyCompatibleB S) && !(S.any b1))
        && !(S.any b2)))

/-! ## 3. The six aggregation identities -/

variable [DecidableEq L.Plaquette]

/-- `Ξ ≃ XiB(b₁) + Av(b₁)`. -/
theorem xi_partition_b1 (w : Q') (qP b1 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiR w qP Γ label).eqv
      (XiB w qP b1 Γ label + XiAvoid w qP b1 Γ label) :=
  polySum_filter_partition label _ (fun S => S.any b1) (sublists Γ)

/-- `XiB(b₁) ≃ XiB2 + D`. -/
theorem xib1_partition (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiB w qP b1 Γ label).eqv
      (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label) := by
  have h := polySum_filter_partition (w := w) label
    (fun S => (S.all qP && familyCompatibleB S) && S.any b1)
    (fun S => S.any b2) (sublists Γ)
  refine Q'.eqv_trans _ _ _ h ?_
  refine add_eqv_congr_both _ _ _ _ ?_ (Q'.eqv_refl _)
  -- ((plain && a1) && a2) ↔ (plain && (a1 && a2))
  refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
  apply List.filter_congr
  intro S _hS
  cases S.all qP && familyCompatibleB S <;> cases S.any b1 <;>
    cases S.any b2 <;> rfl

/-- `Av(b₁) ≃ E + A₁₂`. -/
theorem xiavoid1_partition (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiAvoid w qP b1 Γ label).eqv
      (cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label) :=
  polySum_filter_partition label _ (fun S => S.any b2) (sublists Γ)

/-- `XiB(b₂) ≃ XiB2 + E`. -/
theorem xib2_partition (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiB w qP b2 Γ label).eqv
      (XiB2 w qP b1 b2 Γ label + cellE w qP b1 b2 Γ label) := by
  have h := polySum_filter_partition (w := w) label
    (fun S => (S.all qP && familyCompatibleB S) && S.any b2)
    (fun S => S.any b1) (sublists Γ)
  refine Q'.eqv_trans _ _ _ h ?_
  refine add_eqv_congr_both _ _ _ _ ?_ ?_
  · refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
    apply List.filter_congr
    intro S _hS
    cases S.all qP && familyCompatibleB S <;> cases S.any b1 <;>
      cases S.any b2 <;> rfl
  · refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
    apply List.filter_congr
    intro S _hS
    cases S.all qP && familyCompatibleB S <;> cases S.any b1 <;>
      cases S.any b2 <;> rfl

/-- `Av(b₂) ≃ D + A₁₂`. -/
theorem xiavoid2_partition (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiAvoid w qP b2 Γ label).eqv
      (cellD w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label) := by
  have h := polySum_filter_partition (w := w) label
    (fun S => (S.all qP && familyCompatibleB S) && !(S.any b2))
    (fun S => S.any b1) (sublists Γ)
  refine Q'.eqv_trans _ _ _ h ?_
  refine add_eqv_congr_both _ _ _ _ ?_ ?_
  · refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
    apply List.filter_congr
    intro S _hS
    cases S.all qP && familyCompatibleB S <;> cases S.any b1 <;>
      cases S.any b2 <;> rfl
  · refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
    apply List.filter_congr
    intro S _hS
    cases S.all qP && familyCompatibleB S <;> cases S.any b1 <;>
      cases S.any b2 <;> rfl

/-! ## 4. The 4-variable polynomial core (the RING NORMALISER's payload) -/

/-- LHS syntax: `x₀·(x₀+x₁+x₂+x₃) + (x₂+x₃)·(x₁+x₃)`
(`x₀ = B`, `x₁ = D`, `x₂ = E`, `x₃ = A`). -/
def tpLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)))
    (.mul (.add (.var 2) (.var 3)) (.add (.var 1) (.var 3)))

/-- RHS syntax: `(x₀+x₁)·(x₀+x₂) + x₃·(x₀+x₁+x₂+x₃)`. -/
def tpRHS : PolyExpr :=
  .add
    (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 2)))
    (.mul (.var 3) (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)))

/-- The two sides share the same canonical normal form (kernel computation). -/
theorem tp_normal_eq : normalize tpLHS = normalize tpRHS := by decide

/-- **`cell_expand` (PROVED by the reflective normaliser).**  The 4-variable
degree-2 identity behind the two-point Mayer identity:

    B(B+D+E+A) + (E+A)(D+A)  ≃  (B+D)(B+E) + A(B+D+E+A). -/
theorem cell_expand (B D E A : Q') :
    (B * (B + D + E + A) + (E + A) * (D + A)).eqv
      ((B + D) * (B + E) + A * (B + D + E + A)) := by
  have h := poly_identity_of_normal_eq tpLHS tpRHS tp_normal_eq
    (fun i => if i = 0 then B else if i = 1 then D else if i = 2 then E else A)
  simpa [eval, tpLHS, tpRHS] using h

/-! ## 5. THE TWO-POINT MAYER IDENTITY (subtraction-free) -/

/-- `(x·y) ≃ (x'·y')` from componentwise `eqv`. -/
theorem mul_eqv_congr_both {x x' y y' : Q'} (hx : x.eqv x') (hy : y.eqv y') :
    (x * y).eqv (x' * y') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hx)
    (Q'.mul_eqv_congr_left _ _ _ hy)

/-- **`two_point_mayer` (PROVED — the sign layer as an exact identity).**

    XiB2·Ξ + Av(b₁)·Av(b₂)  ≃  XiB(b₁)·XiB(b₂) + A₁₂·Ξ.

The truncated two-point correlator `XiB2·Ξ − XiB(b₁)·XiB(b₂)` (Ursell-signed)
equals `A₁₂·Ξ − Av(b₁)·Av(b₂)` — stated with no subtraction: an equation
between four nonnegative products of partition sums.  Proof: the four-cell
partition + the normaliser identity `cell_expand`. -/
theorem two_point_mayer (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
        + XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label).eqv
      (XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiR w qP Γ label) := by
  -- the four-cell expansion of Ξ: Ξ ≃ ((B + D) + E) + A
  have hXi : (XiR w qP Γ label).eqv
      (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
        + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label) := by
    refine Q'.eqv_trans _ _ _ (xi_partition_b1 w qP b1 Γ label) ?_
    refine Q'.eqv_trans _ _ _
      (add_eqv_congr_both _ _ _ _ (xib1_partition w qP b1 b2 Γ label)
        (xiavoid1_partition w qP b1 b2 Γ label)) ?_
    -- (B + D) + (E + A) ≃ ((B + D) + E) + A
    exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)
  have hcore := cell_expand (XiB2 w qP b1 b2 Γ label)
    (cellD w qP b1 b2 Γ label) (cellE w qP b1 b2 Γ label)
    (cellA w qP b1 b2 Γ label)
  -- LHS ≃ core-LHS
  have hL : (XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
      + XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label).eqv
      (XiB2 w qP b1 b2 Γ label
          * (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
            + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)
        + (cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)
            * (cellD w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)) :=
    add_eqv_congr_both _ _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hXi)
      (mul_eqv_congr_both (xiavoid1_partition w qP b1 b2 Γ label)
        (xiavoid2_partition w qP b1 b2 Γ label))
  -- core-RHS ≃ RHS
  have hR : ((XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label)
        * (XiB2 w qP b1 b2 Γ label + cellE w qP b1 b2 Γ label)
      + cellA w qP b1 b2 Γ label
          * (XiB2 w qP b1 b2 Γ label + cellD w qP b1 b2 Γ label
            + cellE w qP b1 b2 Γ label + cellA w qP b1 b2 Γ label)).eqv
      (XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiR w qP Γ label) :=
    add_eqv_congr_both _ _ _ _
      (mul_eqv_congr_both
        (Q'.eqv_symm (xib1_partition w qP b1 b2 Γ label))
        (Q'.eqv_symm (xib2_partition w qP b1 b2 Γ label)))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hXi))
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_trans _ _ _ hcore hR)

/-- **`XiB2_mul_le` (PROVED — the truncated-numerator upper bound).**  The
raw truncated numerator is dominated by the product term plus the double-
avoidance term:

    XiB2·Ξ  ≤  XiB(b₁)·XiB(b₂) + A₁₂·Ξ.

The open residual of the whole sign layer is thereby ISOLATED: everything
beyond this is the avoidance-correlation inequality (how much `A₁₂·Ξ`
exceeds `Av(b₁)·Av(b₂)`) — the genuine connected-chain content. -/
theorem XiB2_mul_le {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
      ≤ XiB w qP b1 Γ label * XiB w qP b2 Γ label
        + cellA w qP b1 b2 Γ label * XiR w qP Γ label := by
  have h1 : XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
      ≤ XiB2 w qP b1 b2 Γ label * XiR w qP Γ label
        + XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label :=
    Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (polySum_nonneg hw label _)
        (polySum_nonneg hw label _))
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_of_eqv (two_point_mayer w qP b1 b2 Γ label))

end YMGap.Continuum.XiSignLayer

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.XiSignLayer.polySum_filter_partition
#print axioms YMGap.Continuum.XiSignLayer.xi_partition_b1
#print axioms YMGap.Continuum.XiSignLayer.xib1_partition
#print axioms YMGap.Continuum.XiSignLayer.xiavoid1_partition
#print axioms YMGap.Continuum.XiSignLayer.xib2_partition
#print axioms YMGap.Continuum.XiSignLayer.xiavoid2_partition
#print axioms YMGap.Continuum.XiSignLayer.tp_normal_eq
#print axioms YMGap.Continuum.XiSignLayer.cell_expand
#print axioms YMGap.Continuum.XiSignLayer.two_point_mayer
#print axioms YMGap.Continuum.XiSignLayer.XiB2_mul_le
