/-
`XiChainBound` — Milestone 13.1, D1-loopy step 5: the TWO-MARKER Mayer bound
for the two-point hard-core polymer sums (the raw-pair domination — the next
piece of the Ursell-sign layer after the single-bridge bound of
`XiPinnedBridge`).

# The statement

Mark two `Bool` classes `br₁`, `br₂` (downstream: "covers `p`" / "covers
`q`").  Let `XiB2 w qP br₁ br₂ Γ label` be the restricted, compatibility-
filtered partition sum over sub-families containing AT LEAST ONE `br₁`-marked
AND AT LEAST ONE `br₂`-marked polymer (possibly the same).  Then
(`XiB2_le_chain`):

  XiB2 ≤ actSum(br₁∧br₂)·XiR + actSum(br₁)·XiB(br₂) + actSum(br₂)·XiB(br₁),

i.e. the pair sum splits into the SAME-polymer diagonal (one polymer carries
both marks — the single-bridge term) and the DISTINCT-witness parts, each
dominated by (activity sum of one mark) × (marked sum of the other).
Chaining `XiPinnedBridge.XiB_le_actSum_mul_XiR` into the last two terms gives
the closed product form (`XiB2_le_product`):

  XiB2 ≤ [actSum(br₁∧br₂) + 2·actSum(br₁)·actSum(br₂)]-type bounds,

kept in three-term shape to preserve sharpness.

# Why this is the right increment (honest scope)

The two-point function's numerator `XiCov₂(p,q)` is exactly `XiB2` at the
covering markers: this theorem is the RAW-PAIR Mayer domination — the upper
envelope for `⟨1_p 1_q⟩·Ξ` by bridge + product terms.  What it is NOT: the
TRUNCATED correlator bound (subtracting `XiCov_p·XiCov_q/Ξ`), whose chain
term carries the Ursell SIGNS — that remains the named-open A1 physical
content (a hard-core gas is not negatively correlated; the sign layer is
genuinely deeper).  Fixed volume, no Haar, no continuum; the Clay problem
remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.XiPinnedBridge

namespace YMGap.Continuum.XiChainBound

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPinnedBridge

variable {L : Lattice}

/-! ## 0. Small `Q'` AC helpers -/

/-- `(p + q) + r ≃ (p + r) + q`. -/
theorem swap_mid (p q r : Q') : ((p + q) + r).eqv ((p + r) + q) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv p q r) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv q r)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv p r q)

/-- Pairwise regrouping of two 3-sums:
`(x₁+y₁+z₁) + (x₂+y₂+z₂) ≃ (x₁+x₂) + (y₁+y₂) + (z₁+z₂)`. -/
theorem add3_pair (x1 y1 z1 x2 y2 z2 : Q') :
    ((x1 + y1 + z1) + (x2 + y2 + z2)).eqv
      ((x1 + x2) + (y1 + y2) + (z1 + z2)) := by
  -- absorb x₂ then y₂ then z₂
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (x1 + y1 + z1) (x2 + y2) z2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (x1 + y1 + z1) x2 y2))) ?_
  -- ((x1+y1+z1)+x2) ≃ ((x1+x2)+y1)+z1
  have h1 : ((x1 + y1 + z1) + x2).eqv (((x1 + x2) + y1) + z1) := by
    refine Q'.eqv_trans _ _ _ (swap_mid (x1 + y1) z1 x2) ?_
    exact Q'.add_eqv_congr_right _ _ _ (swap_mid x1 y1 x2)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _ h1)) ?_
  -- ((((x1+x2)+y1)+z1)+y2)+z2 ≃ target
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (swap_mid ((x1 + x2) + y1) z1 y2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.add_assoc_eqv (x1 + x2) y1 y2))) ?_
  exact Q'.add_assoc_eqv ((x1 + x2) + (y1 + y2)) z1 z2

/-- Absorb a trailing summand into the FIRST slot of a 3-sum. -/
theorem add_into_first (x y z t : Q') :
    (((x + y) + z) + t).eqv (((t + x) + y) + z) := by
  refine Q'.eqv_trans _ _ _ (swap_mid (x + y) z t) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv (x + y) t)) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv t x y))

/-- Absorb a trailing summand into the SECOND slot of a 3-sum. -/
theorem add_into_second (x y z t : Q') :
    (((x + y) + z) + t).eqv ((x + (t + y)) + z) := by
  refine Q'.eqv_trans _ _ _ (swap_mid (x + y) z t) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_assoc_eqv x y t)) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv y t))

/-- Absorb a trailing summand into the THIRD slot of a 3-sum. -/
theorem add_into_third (x y z t : Q') :
    (((x + y) + z) + t).eqv ((x + y) + (t + z)) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (x + y) z t) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.add_comm_eqv z t)

/-- `x·(y·z) ≃ y·(x·z)`. -/
theorem mul_swap (x y z : Q') : (x * (y * z)).eqv (y * (x * z)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x y z)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv x y)) ?_
  exact Q'.mul_assoc_eqv y x z

/-! ## 1. The two-marker sum and the `XiB` plumbing completions -/

/-- The two-marker partition sum: compatible, `qP`-restricted sub-families
containing at least one `br₁`-marked AND at least one `br₂`-marked member. -/
def XiB2 [DecidableEq L.Plaquette] (w : Q') (qP br1 br2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter
      (fun S => (S.all qP && familyCompatibleB S) && (S.any br1 && S.any br2)))

theorem XiB_nonneg [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (qP br : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) : (0 : Q') ≤ XiB w qP br Γ label :=
  polySum_nonneg hw label _

/-- `XiB` grows under cons. -/
theorem XiB_le_cons [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (qP br : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiB w qP br Λ label ≤ XiB w qP br (a :: Λ) label := by
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (XiB_cons w qP br a Λ label))
  exact Q'.add_le_self_of_nonneg _ _ (polySum_nonneg hw label _)

/-- `XiB` shrinks under predicate strengthening. -/
theorem XiB_pred_mono [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (qP r br : Polymer L → Bool) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiB w (fun X => qP X && r X) br Λ label ≤ XiB w qP br Λ label := by
  unfold XiB
  refine polySum_filter_mono hw label _ _ ?_ _
  intro S h
  obtain ⟨hall, hany⟩ := (Bool.and_eq_true _ _).mp h
  obtain ⟨hq, hf⟩ := (Bool.and_eq_true _ _).mp hall
  rw [← all_and qP r S] at hq
  obtain ⟨hq1, _⟩ := (Bool.and_eq_true _ _).mp hq
  rw [hq1, hf, hany]
  rfl

/-- The `qP`-passing, non-marked-head cons split of `XiB` (the marked
`any`-conjunct passes to the tail). -/
theorem XiB_cons_split_nobridge [DecidableEq L.Plaquette] (w : Q')
    (qP br : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) (hqa : qP a = true) (hba : br a = false) :
    (XiB w qP br (a :: Λ) label).eqv
      (XiB w qP br Λ label
        + activity w a label
            * XiB w (fun X => qP X && compatibleB a X) br Λ label) := by
  refine Q'.eqv_trans _ _ _ (XiB_cons w qP br a Λ label) ?_
  exact add_eqv_congr_both _ _ _ _ (Q'.eqv_refl _)
    (XiB_mapbranch_nobridge w qP br a Λ label hqa hba)

/-! ## 2. The `XiB2` cons unfolding and the four map-branch cases -/

theorem XiB2_cons [DecidableEq L.Plaquette] (w : Q')
    (qP br1 br2 : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    (XiB2 w qP br1 br2 (a :: Λ) label).eqv
      (XiB2 w qP br1 br2 Λ label
        + polySum w label
            (((sublists Λ).map (fun s => a :: s)).filter
              (fun S => (S.all qP && familyCompatibleB S)
                && (S.any br1 && S.any br2)))) := by
  unfold XiB2
  rw [sublists_cons, List.filter_append]
  exact polySum_append w label _ _

/-- Branch, `qP a = false`: empty. -/
theorem XiB2_mapbranch_none [DecidableEq L.Plaquette]
    (qP br1 br2 : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (hqa : qP a = false) :
    (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S)
          && (S.any br1 && S.any br2))) = [] := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T)
            && (T.any br1 && T.any br2)) (a :: S))
        = (sublists Λ).filter (fun _ => false) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S))
        && ((a :: S).any br1 && (a :: S).any br2)) = false
    rw [List.all_cons, hqa, Bool.false_and, Bool.false_and, Bool.false_and]
  rw [hcongr, filter_const_false, List.map_nil]

/-- Branch, head carries BOTH marks: the plain restricted sum. -/
theorem XiB2_mapbranch_both [DecidableEq L.Plaquette] (w : Q')
    (qP br1 br2 : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep)
    (hqa : qP a = true) (hb1 : br1 a = true) (hb2 : br2 a = true) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S)
          && (S.any br1 && S.any br2)))).eqv
    (activity w a label
      * XiR w (fun X => qP X && compatibleB a X) Λ label) := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T)
            && (T.any br1 && T.any br2)) (a :: S))
        = (sublists Λ).filter
            (fun S => S.all (fun X => qP X && compatibleB a X)
              && familyCompatibleB S) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S))
        && ((a :: S).any br1 && (a :: S).any br2))
        = (S.all (fun X => qP X && compatibleB a X) && familyCompatibleB S)
    rw [List.any_cons, List.any_cons, hb1, hb2, List.all_cons, hqa,
      familyCompatibleB_cons, ← all_and qP (fun Y => compatibleB a Y) S]
    cases S.all qP <;> cases S.all (fun Y => compatibleB a Y) <;>
      cases familyCompatibleB S <;> cases S.any br1 <;> cases S.any br2 <;> rfl
  rw [hcongr]
  exact polySum_map_cons w label a _

/-- Branch, head carries ONLY `br₁`: the `br₂`-marked sum. -/
theorem XiB2_mapbranch_first [DecidableEq L.Plaquette] (w : Q')
    (qP br1 br2 : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep)
    (hqa : qP a = true) (hb1 : br1 a = true) (hb2 : br2 a = false) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S)
          && (S.any br1 && S.any br2)))).eqv
    (activity w a label
      * XiB w (fun X => qP X && compatibleB a X) br2 Λ label) := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T)
            && (T.any br1 && T.any br2)) (a :: S))
        = (sublists Λ).filter
            (fun S => (S.all (fun X => qP X && compatibleB a X)
              && familyCompatibleB S) && S.any br2) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S))
        && ((a :: S).any br1 && (a :: S).any br2))
        = ((S.all (fun X => qP X && compatibleB a X) && familyCompatibleB S)
            && S.any br2)
    rw [List.any_cons, List.any_cons, hb1, hb2, List.all_cons, hqa,
      familyCompatibleB_cons, ← all_and qP (fun Y => compatibleB a Y) S]
    cases S.all qP <;> cases S.all (fun Y => compatibleB a Y) <;>
      cases familyCompatibleB S <;> cases S.any br1 <;> cases S.any br2 <;> rfl
  rw [hcongr]
  exact polySum_map_cons w label a _

/-- Branch, head carries ONLY `br₂`: the `br₁`-marked sum. -/
theorem XiB2_mapbranch_second [DecidableEq L.Plaquette] (w : Q')
    (qP br1 br2 : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep)
    (hqa : qP a = true) (hb1 : br1 a = false) (hb2 : br2 a = true) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S)
          && (S.any br1 && S.any br2)))).eqv
    (activity w a label
      * XiB w (fun X => qP X && compatibleB a X) br1 Λ label) := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T)
            && (T.any br1 && T.any br2)) (a :: S))
        = (sublists Λ).filter
            (fun S => (S.all (fun X => qP X && compatibleB a X)
              && familyCompatibleB S) && S.any br1) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S))
        && ((a :: S).any br1 && (a :: S).any br2))
        = ((S.all (fun X => qP X && compatibleB a X) && familyCompatibleB S)
            && S.any br1)
    rw [List.any_cons, List.any_cons, hb1, hb2, List.all_cons, hqa,
      familyCompatibleB_cons, ← all_and qP (fun Y => compatibleB a Y) S]
    cases S.all qP <;> cases S.all (fun Y => compatibleB a Y) <;>
      cases familyCompatibleB S <;> cases S.any br1 <;> cases S.any br2 <;> rfl
  rw [hcongr]
  exact polySum_map_cons w label a _

/-- Branch, head unmarked: the two-marker sum at the strengthened predicate. -/
theorem XiB2_mapbranch_neither [DecidableEq L.Plaquette] (w : Q')
    (qP br1 br2 : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep)
    (hqa : qP a = true) (hb1 : br1 a = false) (hb2 : br2 a = false) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S)
          && (S.any br1 && S.any br2)))).eqv
    (activity w a label
      * XiB2 w (fun X => qP X && compatibleB a X) br1 br2 Λ label) := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T)
            && (T.any br1 && T.any br2)) (a :: S))
        = (sublists Λ).filter
            (fun S => (S.all (fun X => qP X && compatibleB a X)
              && familyCompatibleB S) && (S.any br1 && S.any br2)) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S))
        && ((a :: S).any br1 && (a :: S).any br2))
        = ((S.all (fun X => qP X && compatibleB a X) && familyCompatibleB S)
            && (S.any br1 && S.any br2))
    rw [List.any_cons, List.any_cons, hb1, hb2, List.all_cons, hqa,
      familyCompatibleB_cons, ← all_and qP (fun Y => compatibleB a Y) S]
    cases S.all qP <;> cases S.all (fun Y => compatibleB a Y) <;>
      cases familyCompatibleB S <;> cases S.any br1 <;> cases S.any br2 <;> rfl
  rw [hcongr]
  exact polySum_map_cons w label a _

/-! ## 3. THE THEOREM: the two-marker chain bound -/

/-- **`XiB2_le_chain` (PROVED — the raw-pair Mayer domination).**

    XiB2 ≤ actSum(br₁∧br₂)·XiR + actSum(br₁)·XiB(br₂) + actSum(br₂)·XiB(br₁).

Structural induction on `Γ` with `qP` generalized; the head is either
unrestricted, doubly marked (feeds the diagonal), singly marked (feeds the
corresponding cross term), or unmarked (recurses). -/
theorem XiB2_le_chain [DecidableEq L.Plaquette] {w : Q'}
    (hw : (0 : Q') ≤ w) (br1 br2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) :
    ∀ (Γ : List (Polymer L)) (qP : Polymer L → Bool),
      XiB2 w qP br1 br2 Γ label
        ≤ actSum w (Γ.filter (fun X => br1 X && br2 X)) label
              * XiR w qP Γ label
          + actSum w (Γ.filter br1) label * XiB w qP br2 Γ label
          + actSum w (Γ.filter br2) label * XiB w qP br1 Γ label
  | [], qP => by
      show (0 : Q') ≤ _
      refine Q'.zero_le_add _ _ (Q'.zero_le_add _ _ ?_ ?_) ?_ <;>
        exact Q'.mul_nonneg _ _ (actSum_nonneg hw _ label)
          (polySum_nonneg hw label _)
  | a :: Λ, qP => by
      have hζ : (0 : Q') ≤ activity w a label := activity_nonneg hw a label
      have hIH := XiB2_le_chain hw br1 br2 label Λ qP
      -- shared cons-monotone triple bound: the Λ-target ≤ the (a::Λ)-target
      have htgt :
          actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                * XiR w qP Λ label
              + actSum w (Λ.filter br1) label * XiB w qP br2 Λ label
              + actSum w (Λ.filter br2) label * XiB w qP br1 Λ label
            ≤ actSum w ((a :: Λ).filter (fun X => br1 X && br2 X)) label
                * XiR w qP (a :: Λ) label
              + actSum w ((a :: Λ).filter br1) label
                  * XiB w qP br2 (a :: Λ) label
              + actSum w ((a :: Λ).filter br2) label
                  * XiB w qP br1 (a :: Λ) label := by
        refine Q'.add_le_add (Q'.add_le_add ?_ ?_) ?_
        · exact Q'.mul_le_mul_of_nonneg
            (actSum_filter_le_cons hw _ a Λ label)
            (XiR_le_cons hw qP a Λ label)
            (actSum_nonneg hw _ label) (XiR_nonneg hw qP Λ label)
        · exact Q'.mul_le_mul_of_nonneg
            (actSum_filter_le_cons hw br1 a Λ label)
            (XiB_le_cons hw qP br2 a Λ label)
            (actSum_nonneg hw _ label) (XiB_nonneg hw qP br2 Λ label)
        · exact Q'.mul_le_mul_of_nonneg
            (actSum_filter_le_cons hw br2 a Λ label)
            (XiB_le_cons hw qP br1 a Λ label)
            (actSum_nonneg hw _ label) (XiB_nonneg hw qP br1 Λ label)
      -- factor-growth facts (Λ-coefficients kept, sum factors grown to a::Λ)
      have hgrow1 : actSum w (Λ.filter (fun X => br1 X && br2 X)) label
            * XiR w qP Λ label
          ≤ actSum w (Λ.filter (fun X => br1 X && br2 X)) label
            * XiR w qP (a :: Λ) label :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ (XiR_le_cons hw qP a Λ label)
          (actSum_nonneg hw _ label)
      have hgrow2 : actSum w (Λ.filter br1) label * XiB w qP br2 Λ label
          ≤ actSum w (Λ.filter br1) label * XiB w qP br2 (a :: Λ) label :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ (XiB_le_cons hw qP br2 a Λ label)
          (actSum_nonneg hw _ label)
      have hgrow3 : actSum w (Λ.filter br2) label * XiB w qP br1 Λ label
          ≤ actSum w (Λ.filter br2) label * XiB w qP br1 (a :: Λ) label :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ (XiB_le_cons hw qP br1 a Λ label)
          (actSum_nonneg hw _ label)
      cases hqa : qP a with
      | false =>
          have hXiB2 : (XiB2 w qP br1 br2 (a :: Λ) label).eqv
              (XiB2 w qP br1 br2 Λ label) := by
            refine Q'.eqv_trans _ _ _ (XiB2_cons w qP br1 br2 a Λ label) ?_
            rw [XiB2_mapbranch_none qP br1 br2 a Λ hqa, polySum_nil]
            exact Q'.eqv_of_eq (Q'.add_zero' _)
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hXiB2)
            (Q'.le_trans' _ _ _ hIH htgt)
      | true =>
          cases hb1 : br1 a with
          | true =>
              cases hb2 : br2 a with
              | true =>
                  -- DOUBLY marked head → the diagonal slot
                  have hact12 : actSum w
                        ((a :: Λ).filter (fun X => br1 X && br2 X)) label
                      = activity w a label
                        + actSum w (Λ.filter (fun X => br1 X && br2 X)) label := by
                    rw [List.filter_cons, if_pos (by rw [hb1, hb2]; rfl),
                      actSum_cons]
                  -- branch ≤ ζa · XiR(a::Λ)
                  have hbrle : polySum w label
                        (((sublists Λ).map (fun s => a :: s)).filter
                          (fun S => (S.all qP && familyCompatibleB S)
                            && (S.any br1 && S.any br2)))
                      ≤ activity w a label * XiR w qP (a :: Λ) label := by
                    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
                      (XiB2_mapbranch_both w qP br1 br2 a Λ label hqa hb1 hb2)) ?_
                    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hζ
                    exact Q'.le_trans' _ _ _
                      (XiR_pred_mono hw qP (fun X => compatibleB a X) Λ label)
                      (XiR_le_cons hw qP a Λ label)
                  -- assemble: IH + grow + fold ζa into slot 1
                  have hbound : XiB2 w qP br1 br2 (a :: Λ) label
                      ≤ (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                            * XiR w qP (a :: Λ) label
                          + actSum w (Λ.filter br1) label
                              * XiB w qP br2 (a :: Λ) label
                          + actSum w (Λ.filter br2) label
                              * XiB w qP br1 (a :: Λ) label)
                        + activity w a label * XiR w qP (a :: Λ) label := by
                    refine Q'.le_trans' _ _ _
                      (Q'.le_of_eqv (XiB2_cons w qP br1 br2 a Λ label)) ?_
                    refine Q'.add_le_add ?_ hbrle
                    exact Q'.le_trans' _ _ _ hIH
                      (Q'.add_le_add (Q'.add_le_add hgrow1 hgrow2) hgrow3)
                  refine Q'.le_trans' _ _ _ hbound ?_
                  rw [hact12]
                  -- regroup t into slot 1, fold (ζa + aS12)·X', GROW slots 2,3
                  have hre : (((actSum w
                          (Λ.filter (fun X => br1 X && br2 X)) label
                            * XiR w qP (a :: Λ) label
                        + actSum w (Λ.filter br1) label
                            * XiB w qP br2 (a :: Λ) label)
                        + actSum w (Λ.filter br2) label
                            * XiB w qP br1 (a :: Λ) label)
                      + activity w a label * XiR w qP (a :: Λ) label).eqv
                      ((((activity w a label
                            + actSum w (Λ.filter (fun X => br1 X && br2 X)) label)
                          * XiR w qP (a :: Λ) label
                        + actSum w (Λ.filter br1) label
                            * XiB w qP br2 (a :: Λ) label)
                        + actSum w (Λ.filter br2) label
                            * XiB w qP br1 (a :: Λ) label)) := by
                    refine Q'.eqv_trans _ _ _ (add_into_first _ _ _ _) ?_
                    refine add_eqv_congr_both _ _ _ _
                      (add_eqv_congr_both _ _ _ _ ?_ (Q'.eqv_refl _))
                      (Q'.eqv_refl _)
                    exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
                  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_
                  refine Q'.add_le_add (Q'.add_le_add (Q'.le_refl' _) ?_) ?_
                  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
                      (actSum_filter_le_cons hw br1 a Λ label)
                      (XiB_nonneg hw qP br2 (a :: Λ) label)
                  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
                      (actSum_filter_le_cons hw br2 a Λ label)
                      (XiB_nonneg hw qP br1 (a :: Λ) label)
              | false =>
                  -- ONLY br₁ head → the second slot
                  have hact12 : actSum w
                        ((a :: Λ).filter (fun X => br1 X && br2 X)) label
                      = actSum w (Λ.filter (fun X => br1 X && br2 X)) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb1, hb2]; exact Bool.false_ne_true)]
                  have hact1 : actSum w ((a :: Λ).filter br1) label
                      = activity w a label + actSum w (Λ.filter br1) label := by
                    rw [List.filter_cons, if_pos hb1, actSum_cons]
                  have hact2 : actSum w ((a :: Λ).filter br2) label
                      = actSum w (Λ.filter br2) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb2]; exact Bool.false_ne_true)]
                  have hbrle : polySum w label
                        (((sublists Λ).map (fun s => a :: s)).filter
                          (fun S => (S.all qP && familyCompatibleB S)
                            && (S.any br1 && S.any br2)))
                      ≤ activity w a label * XiB w qP br2 (a :: Λ) label := by
                    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
                      (XiB2_mapbranch_first w qP br1 br2 a Λ label hqa hb1 hb2)) ?_
                    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hζ
                    exact Q'.le_trans' _ _ _
                      (XiB_pred_mono hw qP (fun X => compatibleB a X) br2 Λ label)
                      (XiB_le_cons hw qP br2 a Λ label)
                  have hbound : XiB2 w qP br1 br2 (a :: Λ) label
                      ≤ (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                            * XiR w qP (a :: Λ) label
                          + actSum w (Λ.filter br1) label
                              * XiB w qP br2 (a :: Λ) label
                          + actSum w (Λ.filter br2) label
                              * XiB w qP br1 (a :: Λ) label)
                        + activity w a label * XiB w qP br2 (a :: Λ) label := by
                    refine Q'.le_trans' _ _ _
                      (Q'.le_of_eqv (XiB2_cons w qP br1 br2 a Λ label)) ?_
                    refine Q'.add_le_add ?_ hbrle
                    exact Q'.le_trans' _ _ _ hIH
                      (Q'.add_le_add (Q'.add_le_add hgrow1 hgrow2) hgrow3)
                  refine Q'.le_trans' _ _ _ hbound ?_
                  rw [hact12, hact1, hact2]
                  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
                    (add_into_second _ _ _ _) ?_)
                  refine add_eqv_congr_both _ _ _ _
                    (add_eqv_congr_both _ _ _ _ (Q'.eqv_refl _) ?_)
                    (Q'.eqv_refl _)
                  exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
          | false =>
              cases hb2 : br2 a with
              | true =>
                  -- ONLY br₂ head → the third slot
                  have hact12 : actSum w
                        ((a :: Λ).filter (fun X => br1 X && br2 X)) label
                      = actSum w (Λ.filter (fun X => br1 X && br2 X)) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb1]; exact Bool.false_ne_true)]
                  have hact1 : actSum w ((a :: Λ).filter br1) label
                      = actSum w (Λ.filter br1) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb1]; exact Bool.false_ne_true)]
                  have hact2 : actSum w ((a :: Λ).filter br2) label
                      = activity w a label + actSum w (Λ.filter br2) label := by
                    rw [List.filter_cons, if_pos hb2, actSum_cons]
                  have hbrle : polySum w label
                        (((sublists Λ).map (fun s => a :: s)).filter
                          (fun S => (S.all qP && familyCompatibleB S)
                            && (S.any br1 && S.any br2)))
                      ≤ activity w a label * XiB w qP br1 (a :: Λ) label := by
                    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
                      (XiB2_mapbranch_second w qP br1 br2 a Λ label hqa hb1 hb2)) ?_
                    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hζ
                    exact Q'.le_trans' _ _ _
                      (XiB_pred_mono hw qP (fun X => compatibleB a X) br1 Λ label)
                      (XiB_le_cons hw qP br1 a Λ label)
                  have hbound : XiB2 w qP br1 br2 (a :: Λ) label
                      ≤ (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                            * XiR w qP (a :: Λ) label
                          + actSum w (Λ.filter br1) label
                              * XiB w qP br2 (a :: Λ) label
                          + actSum w (Λ.filter br2) label
                              * XiB w qP br1 (a :: Λ) label)
                        + activity w a label * XiB w qP br1 (a :: Λ) label := by
                    refine Q'.le_trans' _ _ _
                      (Q'.le_of_eqv (XiB2_cons w qP br1 br2 a Λ label)) ?_
                    refine Q'.add_le_add ?_ hbrle
                    exact Q'.le_trans' _ _ _ hIH
                      (Q'.add_le_add (Q'.add_le_add hgrow1 hgrow2) hgrow3)
                  refine Q'.le_trans' _ _ _ hbound ?_
                  rw [hact12, hact1, hact2]
                  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
                    (add_into_third _ _ _ _) ?_)
                  refine add_eqv_congr_both _ _ _ _ (Q'.eqv_refl _) ?_
                  exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
              | false =>
                  -- UNMARKED head → recurse at the strengthened predicate
                  have hIH' := XiB2_le_chain hw br1 br2 label Λ
                    (fun X => qP X && compatibleB a X)
                  have hact12 : actSum w
                        ((a :: Λ).filter (fun X => br1 X && br2 X)) label
                      = actSum w (Λ.filter (fun X => br1 X && br2 X)) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb1]; exact Bool.false_ne_true)]
                  have hact1 : actSum w ((a :: Λ).filter br1) label
                      = actSum w (Λ.filter br1) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb1]; exact Bool.false_ne_true)]
                  have hact2 : actSum w ((a :: Λ).filter br2) label
                      = actSum w (Λ.filter br2) label := by
                    rw [List.filter_cons,
                      if_neg (by rw [hb2]; exact Bool.false_ne_true)]
                  -- branch ≤ ζa · (three-term bound at qP')
                  have hbrle : polySum w label
                        (((sublists Λ).map (fun s => a :: s)).filter
                          (fun S => (S.all qP && familyCompatibleB S)
                            && (S.any br1 && S.any br2)))
                      ≤ activity w a label
                          * (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                                * XiR w (fun X => qP X && compatibleB a X) Λ label
                              + actSum w (Λ.filter br1) label
                                  * XiB w (fun X => qP X && compatibleB a X)
                                      br2 Λ label
                              + actSum w (Λ.filter br2) label
                                  * XiB w (fun X => qP X && compatibleB a X)
                                      br1 Λ label) := by
                    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv
                      (XiB2_mapbranch_neither w qP br1 br2 a Λ label
                        hqa hb1 hb2)) ?_
                    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hIH' hζ
                  -- distribute ζa, swap it inside each product
                  have hdist : (activity w a label
                        * (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                              * XiR w (fun X => qP X && compatibleB a X) Λ label
                            + actSum w (Λ.filter br1) label
                                * XiB w (fun X => qP X && compatibleB a X)
                                    br2 Λ label
                            + actSum w (Λ.filter br2) label
                                * XiB w (fun X => qP X && compatibleB a X)
                                    br1 Λ label)).eqv
                      (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                            * (activity w a label
                              * XiR w (fun X => qP X && compatibleB a X) Λ label)
                          + actSum w (Λ.filter br1) label
                              * (activity w a label
                                * XiB w (fun X => qP X && compatibleB a X)
                                    br2 Λ label)
                          + actSum w (Λ.filter br2) label
                              * (activity w a label
                                * XiB w (fun X => qP X && compatibleB a X)
                                    br1 Λ label)) := by
                    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
                    refine Q'.eqv_trans _ _ _
                      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv _ _ _)) ?_
                    refine add_eqv_congr_both _ _ _ _
                      (add_eqv_congr_both _ _ _ _ (mul_swap _ _ _)
                        (mul_swap _ _ _))
                      (mul_swap _ _ _)
                  -- pair the two 3-sums and fold via the cons splits
                  have hsplit1 := XiR_cons_split_true w qP a Λ label hqa
                  have hsplit2 := XiB_cons_split_nobridge w qP br2 a Λ label
                    hqa hb2
                  have hsplit3 := XiB_cons_split_nobridge w qP br1 a Λ label
                    hqa hb1
                  have hbound : XiB2 w qP br1 br2 (a :: Λ) label
                      ≤ (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                            * XiR w qP Λ label
                          + actSum w (Λ.filter br1) label
                              * XiB w qP br2 Λ label
                          + actSum w (Λ.filter br2) label
                              * XiB w qP br1 Λ label)
                        + (actSum w (Λ.filter (fun X => br1 X && br2 X)) label
                              * (activity w a label
                                * XiR w (fun X => qP X && compatibleB a X) Λ label)
                            + actSum w (Λ.filter br1) label
                                * (activity w a label
                                  * XiB w (fun X => qP X && compatibleB a X)
                                      br2 Λ label)
                            + actSum w (Λ.filter br2) label
                                * (activity w a label
                                  * XiB w (fun X => qP X && compatibleB a X)
                                      br1 Λ label)) := by
                    refine Q'.le_trans' _ _ _
                      (Q'.le_of_eqv (XiB2_cons w qP br1 br2 a Λ label)) ?_
                    refine Q'.add_le_add hIH ?_
                    exact Q'.le_trans' _ _ _ hbrle (Q'.le_of_eqv hdist)
                  refine Q'.le_trans' _ _ _ hbound ?_
                  rw [hact12, hact1, hact2]
                  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
                    (add3_pair _ _ _ _ _ _) ?_)
                  refine add_eqv_congr_both _ _ _ _
                    (add_eqv_congr_both _ _ _ _ ?_ ?_) ?_
                  · refine Q'.eqv_trans _ _ _
                      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
                    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hsplit1)
                  · refine Q'.eqv_trans _ _ _
                      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
                    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hsplit2)
                  · refine Q'.eqv_trans _ _ _
                      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
                    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hsplit3)

/-! ## 4. The closed product corollary and the two-point instantiation -/

/-- **`XiB2_le_product` (PROVED).**  Chaining the single-bridge bound into
the cross terms: the raw pair sum is dominated by
`[diagonal + cross-products] · XiR`-type terms with every factor an
activity sum. -/
theorem XiB2_le_product [DecidableEq L.Plaquette] {w : Q'}
    (hw : (0 : Q') ≤ w) (br1 br2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (Γ : List (Polymer L))
    (qP : Polymer L → Bool) :
    XiB2 w qP br1 br2 Γ label
      ≤ actSum w (Γ.filter (fun X => br1 X && br2 X)) label
            * XiR w qP Γ label
        + actSum w (Γ.filter br1) label
            * (actSum w (Γ.filter br2) label * XiR w qP Γ label)
        + actSum w (Γ.filter br2) label
            * (actSum w (Γ.filter br1) label * XiR w qP Γ label) := by
  refine Q'.le_trans' _ _ _ (XiB2_le_chain hw br1 br2 label Γ qP) ?_
  refine Q'.add_le_add (Q'.add_le_add (Q'.le_refl' _) ?_) ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (XiB_le_actSum_mul_XiR hw br2 label Γ qP) (actSum_nonneg hw _ label)
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (XiB_le_actSum_mul_XiR hw br1 label Γ qP) (actSum_nonneg hw _ label)

/-- The single-plaquette covering marker. -/
def coversB [DecidableEq L.Plaquette] (p : L.Plaquette) (X : Polymer L) : Bool :=
  decide (p ∈ X)

/-- **`XiPair_le` (PROVED — the two-point raw-pair Mayer domination).**  The
compatible sub-families covering BOTH `p` and `q` (by one polymer or two)
are dominated by the diagonal (single-bridge) term plus the two cross
products — the exact upper envelope of `⟨1_p 1_q⟩ · Ξ` the (D1) chain needs
above the single-bridge term of `XiPinnedBridge`. -/
theorem XiPair_le [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (p q : L.Plaquette) (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (qP : Polymer L → Bool) :
    XiB2 w qP (coversB p) (coversB q) Γ label
      ≤ actSum w (Γ.filter (fun X => coversB p X && coversB q X)) label
            * XiR w qP Γ label
        + actSum w (Γ.filter (coversB p)) label
            * (actSum w (Γ.filter (coversB q)) label * XiR w qP Γ label)
        + actSum w (Γ.filter (coversB q)) label
            * (actSum w (Γ.filter (coversB p)) label * XiR w qP Γ label) :=
  XiB2_le_product hw (coversB p) (coversB q) label Γ qP

end YMGap.Continuum.XiChainBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.XiChainBound.swap_mid
#print axioms YMGap.Continuum.XiChainBound.add3_pair
#print axioms YMGap.Continuum.XiChainBound.mul_swap
#print axioms YMGap.Continuum.XiChainBound.XiB_le_cons
#print axioms YMGap.Continuum.XiChainBound.XiB_pred_mono
#print axioms YMGap.Continuum.XiChainBound.XiB_cons_split_nobridge
#print axioms YMGap.Continuum.XiChainBound.XiB2_cons
#print axioms YMGap.Continuum.XiChainBound.XiB2_mapbranch_none
#print axioms YMGap.Continuum.XiChainBound.XiB2_mapbranch_both
#print axioms YMGap.Continuum.XiChainBound.XiB2_mapbranch_first
#print axioms YMGap.Continuum.XiChainBound.XiB2_mapbranch_second
#print axioms YMGap.Continuum.XiChainBound.XiB2_mapbranch_neither
#print axioms YMGap.Continuum.XiChainBound.XiB2_le_chain
#print axioms YMGap.Continuum.XiChainBound.XiB2_le_product
#print axioms YMGap.Continuum.XiChainBound.XiPair_le
