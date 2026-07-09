/-
`XiPinnedBridge` — the ONE-POLYMER-BRIDGE (leading Mayer) bound for the
two-point hard-core polymer sums (Milestone 13.1, D1-loopy step 4 — the first
piece of the Ursell-sign layer named in `notes/d1-loopy-closure.md`).

# The statement

For the abstract hard-core polymer gas of `AbstractPolymerXi`, mark an
arbitrary `Bool` class of polymers `br` (instantiated downstream as "covers
both plaquettes `p` and `q`", i.e. the ONE-polymer bridges of the two-point
function).  Let

  `XiB w qP br Γ label` = the `qP`-restricted, compatibility-filtered partition
  sum over the sub-families of `Γ` CONTAINING AT LEAST ONE marked polymer,

the marked (bridging) part of the two-point `Ξ`-sum.  Then

  `XiB w qP br Γ label  ≤  (Σ_{X ∈ Γ.filter br} ζ(X)) · XiR w qP Γ label`

(`XiB_le_actSum_mul_XiR`): the bridging families are dominated by (sum of
bridge activities) × (FULL partition function).  This is the leading
("single-bridge") term of the Mayer two-point expansion, in exactly the form
the (D1) chain consumes: the marked-activity sum over the z4 instance is the
bridging-animal sum whose size floor and KP domination were proved in
`LoopyPinnedPenroseUrsell` (grades `≤ dist` vanish; termwise `≤ kpTerm`).

# Why this is the right next increment (honest scope)

The two-point truncated function of the gas is
`XiCov₂/Ξ − (XiCov_p/Ξ)(XiCov_q/Ξ)`; its Mayer expansion splits into the
SAME-polymer (bridge) part — bounded HERE — and the connected-CHAIN part
(overlapping polymer chains from `p` to `q`), which carries the Ursell signs
and remains NAMED-OPEN (it is the genuine A1 physical content; a hard-core
gas is NOT negatively correlated in general — a polymer overlapping both
sources creates positive correlation, which is exactly the chain term).
Nothing here touches the Haar/abstract↔real identity (R1) or the continuum.
The Clay Yang–Mills mass gap remains OPEN.

# Proof shape (finite combinatorics, no Haar, no signs)

Structural induction on `Γ` with the restriction predicate `qP` generalized
(the add-one step strengthens `qP` to `qP && compatibleB a`, exactly as in
`XiR_eq_Xi_filter`).  The three add-one cases:

  * `qP a = false` — the `(a::·)` branch is empty (mirror of
    `XiR_cons_mapbranch_false`);
  * `qP a = true, br a = true` — the branch's `any`-conjunct is satisfied by
    the head, so the branch is `ζ(a) · XiR (qP && cB a) Λ` (mirror of
    `XiR_cons_mapbranch_true`) and folds into the NEW bridge activity `ζ(a)`;
  * `qP a = true, br a = false` — the `any`-conjunct passes to the tail, the
    branch is `ζ(a) · XiB (qP && cB a) br Λ`, and the induction hypothesis at
    the strengthened predicate closes it.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no `Real`,
no `native_decide`, no `by_contra`, no `sorry` / `admit` / new `axiom`.
Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).
-/

import YMGap.Continuum.AbstractPolymerXi

namespace YMGap.Continuum.XiPinnedBridge

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi

variable {L : Lattice}

/-! ## 1. The marked-bridge partition sum and the bridge-activity sum -/

/-- The marked (bridging) part of the restricted partition sum: compatible,
`qP`-restricted sub-families of `Γ` containing AT LEAST ONE `br`-marked
polymer. -/
def XiB [DecidableEq L.Plaquette] (w : Q') (qP br : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polySum w label
    ((sublists Γ).filter
      (fun S => (S.all qP && familyCompatibleB S) && S.any br))

/-- The plain activity sum over a polymer list. -/
def actSum (w : Q') (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  Γ.foldr (fun X acc => activity w X label + acc) 0

@[simp] theorem actSum_nil (w : Q') (label : L.Plaquette → Rep) :
    actSum w ([] : List (Polymer L)) label = 0 := rfl

@[simp] theorem actSum_cons (w : Q') (X : Polymer L) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    actSum w (X :: Γ) label = activity w X label + actSum w Γ label := rfl

theorem actSum_nonneg {w : Q'} (hw : (0 : Q') ≤ w)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ actSum w Γ label := by
  induction Γ with
  | nil => exact Q'.le_refl' 0
  | cons X Γ ih =>
      exact Q'.zero_le_add _ _ (activity_nonneg hw X label) ih

/-! ## 2. Add-one plumbing: the cons unfolding and the three branch cases -/

/-- The raw cons unfolding of `XiB`: omit the head (the `Λ`-sum) plus the
`(a::·)`-prepended branch. -/
theorem XiB_cons [DecidableEq L.Plaquette] (w : Q') (qP br : Polymer L → Bool)
    (a : Polymer L) (Λ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (XiB w qP br (a :: Λ) label).eqv
      (XiB w qP br Λ label
        + polySum w label
            (((sublists Λ).map (fun s => a :: s)).filter
              (fun S => (S.all qP && familyCompatibleB S) && S.any br))) := by
  unfold XiB
  rw [sublists_cons, List.filter_append]
  exact polySum_append w label _ _

/-- Branch case `qP a = false`: nothing survives. -/
theorem XiB_mapbranch_none [DecidableEq L.Plaquette]
    (qP br : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (hqa : qP a = false) :
    (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S) && S.any br)) = [] := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T) && T.any br)
            (a :: S))
        = (sublists Λ).filter (fun _ => false) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S)) && (a :: S).any br)
        = false
    rw [List.all_cons, hqa, Bool.false_and, Bool.false_and, Bool.false_and]
  rw [hcongr, filter_const_false, List.map_nil]

/-- Branch case `qP a = true`, `br a = true`: the head IS a bridge, the
`any`-conjunct is satisfied, and the branch is the plain restricted
partition sum at the strengthened predicate, weighted by `ζ(a)`. -/
theorem XiB_mapbranch_bridge [DecidableEq L.Plaquette]
    (w : Q') (qP br : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep)
    (hqa : qP a = true) (hba : br a = true) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S) && S.any br))).eqv
    (activity w a label
      * XiR w (fun X => qP X && compatibleB a X) Λ label) := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T) && T.any br)
            (a :: S))
        = (sublists Λ).filter
            (fun S => S.all (fun X => qP X && compatibleB a X)
              && familyCompatibleB S) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S)) && (a :: S).any br)
        = (S.all (fun X => qP X && compatibleB a X) && familyCompatibleB S)
    rw [List.any_cons, hba, Bool.true_or, Bool.and_true]
    rw [List.all_cons, hqa, Bool.true_and, familyCompatibleB_cons]
    rw [← Bool.and_assoc, all_and qP (fun Y => compatibleB a Y) S]
  rw [hcongr]
  exact polySum_map_cons w label a _

/-- Branch case `qP a = true`, `br a = false`: the `any`-conjunct passes to
the tail — the branch is the MARKED sum at the strengthened predicate,
weighted by `ζ(a)`. -/
theorem XiB_mapbranch_nobridge [DecidableEq L.Plaquette]
    (w : Q') (qP br : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep)
    (hqa : qP a = true) (hba : br a = false) :
    (polySum w label
      (((sublists Λ).map (fun s => a :: s)).filter
        (fun S => (S.all qP && familyCompatibleB S) && S.any br))).eqv
    (activity w a label
      * XiB w (fun X => qP X && compatibleB a X) br Λ label) := by
  rw [filter_map_cons]
  have hcongr :
      (sublists Λ).filter
          (fun S => (fun T => (T.all qP && familyCompatibleB T) && T.any br)
            (a :: S))
        = (sublists Λ).filter
            (fun S => (S.all (fun X => qP X && compatibleB a X)
              && familyCompatibleB S) && S.any br) := by
    apply List.filter_congr
    intro S _hS
    show (((a :: S).all qP && familyCompatibleB (a :: S)) && (a :: S).any br)
        = ((S.all (fun X => qP X && compatibleB a X) && familyCompatibleB S)
            && S.any br)
    rw [List.any_cons, hba, Bool.false_or]
    rw [List.all_cons, hqa, Bool.true_and, familyCompatibleB_cons]
    rw [← Bool.and_assoc, all_and qP (fun Y => compatibleB a Y) S]
  rw [hcongr]
  exact polySum_map_cons w label a _

/-- The `qP`-restricted cons split for `XiR` at a `qP`-passing head (derived
directly from the §6 branch lemmas of `AbstractPolymerXi` — no detour through
`XiR_eq_Xi_filter`). -/
theorem XiR_cons_split_true [DecidableEq L.Plaquette]
    (w : Q') (qP : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep) (hqa : qP a = true) :
    (XiR w qP (a :: Λ) label).eqv
      (XiR w qP Λ label
        + activity w a label
            * XiR w (fun X => qP X && compatibleB a X) Λ label) := by
  have hLHS :
      (XiR w qP (a :: Λ) label).eqv
        (XiR w qP Λ label
          + polySum w label
              (((sublists Λ).map (fun s => a :: s)).filter
                (fun S => S.all qP && familyCompatibleB S))) := by
    unfold XiR
    rw [sublists_cons, List.filter_append]
    exact polySum_append w label _ _
  refine Q'.eqv_trans _ _ _ hLHS ?_
  exact add_eqv_congr_both _ _ _ _ (Q'.eqv_refl _)
    (XiR_cons_mapbranch_true w qP a Λ label hqa)

/-- `XiR` grows under cons: `XiR qP Λ ≤ XiR qP (a::Λ)` (the added branch is a
nonnegative `polySum`). -/
theorem XiR_le_cons [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (qP : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiR w qP Λ label ≤ XiR w qP (a :: Λ) label := by
  have hLHS :
      (XiR w qP (a :: Λ) label).eqv
        (XiR w qP Λ label
          + polySum w label
              (((sublists Λ).map (fun s => a :: s)).filter
                (fun S => S.all qP && familyCompatibleB S))) := by
    unfold XiR
    rw [sublists_cons, List.filter_append]
    exact polySum_append w label _ _
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hLHS)
  exact Q'.add_le_self_of_nonneg _ _ (polySum_nonneg hw label _)

/-- `XiR` shrinks under predicate strengthening:
`XiR (qP && r) Λ ≤ XiR qP Λ`. -/
theorem XiR_pred_mono [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (qP r : Polymer L → Bool) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiR w (fun X => qP X && r X) Λ label ≤ XiR w qP Λ label := by
  have hff : Λ.filter (fun X => qP X && r X)
      = (Λ.filter qP).filter (fun X => r X) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro X _hX
    exact Bool.and_comm (qP X) (r X)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (XiR_eq_Xi_filter w label (fun X => qP X && r X) Λ)) ?_
  rw [hff]
  refine Q'.le_trans' _ _ _
    (Xi_filter_le hw (fun X => r X) (Λ.filter qP) label) ?_
  exact Q'.ge_of_eqv (XiR_eq_Xi_filter w label qP Λ)

/-- The filtered activity sum grows under cons (whether or not the head is
marked). -/
theorem actSum_filter_le_cons {w : Q'} (hw : (0 : Q') ≤ w)
    (br : Polymer L → Bool) (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    actSum w (Λ.filter br) label ≤ actSum w ((a :: Λ).filter br) label := by
  cases hba : br a with
  | false =>
      rw [List.filter_cons, if_neg (by rw [hba]; exact Bool.false_ne_true)]
      exact Q'.le_refl' _
  | true =>
      rw [List.filter_cons, if_pos hba, actSum_cons]
      have h0 : (0 : Q') + actSum w (Λ.filter br) label
          ≤ activity w a label + actSum w (Λ.filter br) label :=
        Q'.add_le_add_right _ _ _ (activity_nonneg hw a label)
      rwa [Q'.zero_add'] at h0

/-! ## 3. THE THEOREM: the single-bridge bound -/

/-- **`XiB_le_actSum_mul_XiR` (PROVED — the one-polymer-bridge Mayer bound).**

    XiB w qP br Γ label  ≤  actSum w (Γ.filter br) label · XiR w qP Γ label :

the compatible sub-families containing at least one marked (bridging) polymer
are dominated by the sum of marked activities times the FULL restricted
partition function.  Structural induction on `Γ`, `qP` generalized. -/
theorem XiB_le_actSum_mul_XiR [DecidableEq L.Plaquette] {w : Q'}
    (hw : (0 : Q') ≤ w) (br : Polymer L → Bool) (label : L.Plaquette → Rep) :
    ∀ (Γ : List (Polymer L)) (qP : Polymer L → Bool),
      XiB w qP br Γ label
        ≤ actSum w (Γ.filter br) label * XiR w qP Γ label
  | [], qP => by
      show (0 : Q') ≤ actSum w ([].filter br) label * XiR w qP [] label
      exact Q'.le_trans' _ _ _ (Q'.le_refl' 0)
        (Q'.ge_of_eqv (Q'.zero_mul_eqv _))
  | a :: Λ, qP => by
      -- abbreviations
      have hA : (0 : Q') ≤ XiR w qP Λ label := XiR_nonneg hw qP Λ label
      have hζ : (0 : Q') ≤ activity w a label := activity_nonneg hw a label
      have haS : (0 : Q') ≤ actSum w (Λ.filter br) label :=
        actSum_nonneg hw _ label
      have hIH := XiB_le_actSum_mul_XiR hw br label Λ qP
      cases hqa : qP a with
      | false =>
          -- branch empty: XiB (a::Λ) ≃ XiB Λ; grow both factors on the right
          have hbranch := XiB_mapbranch_none qP br a Λ hqa
          have hXiB : (XiB w qP br (a :: Λ) label).eqv (XiB w qP br Λ label) := by
            refine Q'.eqv_trans _ _ _ (XiB_cons w qP br a Λ label) ?_
            rw [hbranch, polySum_nil]
            exact Q'.eqv_of_eq (Q'.add_zero' _)
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hXiB) ?_
          refine Q'.le_trans' _ _ _ hIH ?_
          -- aS·XiR Λ ≤ aS'·XiR (a::Λ)
          refine Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ _
              (XiR_le_cons hw qP a Λ label) haS) ?_
          exact Q'.mul_le_mul_of_nonneg_right _ _ _
            (actSum_filter_le_cons hw br a Λ label)
            (XiR_nonneg hw qP (a :: Λ) label)
      | true =>
          -- the restricted split of the RIGHT factor
          have hsplit := XiR_cons_split_true w qP a Λ label hqa
          cases hba : br a with
          | true =>
              -- XiB (a::Λ) ≃ XiB Λ + ζa·XiR qP' Λ ≤ aS·A + ζa·A
              --   ≃ (ζa+aS)·A ≤ (ζa+aS)·XiR (a::Λ) = actSum'·XiR (a::Λ)
              have hbranch :=
                XiB_mapbranch_bridge w qP br a Λ label hqa hba
              have h1 : XiB w qP br (a :: Λ) label
                  ≤ actSum w (Λ.filter br) label * XiR w qP Λ label
                    + activity w a label
                        * XiR w (fun X => qP X && compatibleB a X) Λ label := by
                refine Q'.le_trans' _ _ _
                  (Q'.le_of_eqv (XiB_cons w qP br a Λ label)) ?_
                exact Q'.add_le_add hIH (Q'.le_of_eqv hbranch)
              -- ζa·XiR qP' ≤ ζa·XiR qP
              have h2 : activity w a label
                    * XiR w (fun X => qP X && compatibleB a X) Λ label
                  ≤ activity w a label * XiR w qP Λ label :=
                Q'.mul_le_mul_of_nonneg_left _ _ _
                  (XiR_pred_mono hw qP (fun X => compatibleB a X) Λ label) hζ
              -- assemble (ζa + aS)·A
              have h3 : actSum w (Λ.filter br) label * XiR w qP Λ label
                    + activity w a label * XiR w qP Λ label
                  = actSum w (Λ.filter br) label * XiR w qP Λ label
                    + activity w a label * XiR w qP Λ label := rfl
              have hsum : (actSum w (Λ.filter br) label * XiR w qP Λ label
                    + activity w a label * XiR w qP Λ label).eqv
                  ((activity w a label + actSum w (Λ.filter br) label)
                    * XiR w qP Λ label) := by
                refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
                exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
              have h4 : XiB w qP br (a :: Λ) label
                  ≤ (activity w a label + actSum w (Λ.filter br) label)
                      * XiR w qP Λ label := by
                refine Q'.le_trans' _ _ _ h1 ?_
                refine Q'.le_trans' _ _ _
                  (Q'.add_le_add (Q'.le_refl' _) h2) ?_
                exact Q'.le_of_eqv hsum
              -- grow the right factor to XiR (a::Λ), match actSum'
              have hζaS : (0 : Q')
                  ≤ activity w a label + actSum w (Λ.filter br) label :=
                Q'.zero_le_add _ _ hζ haS
              have h5 : (activity w a label + actSum w (Λ.filter br) label)
                    * XiR w qP Λ label
                  ≤ (activity w a label + actSum w (Λ.filter br) label)
                      * XiR w qP (a :: Λ) label :=
                Q'.mul_le_mul_of_nonneg_left _ _ _
                  (XiR_le_cons hw qP a Λ label) hζaS
              have hact : actSum w ((a :: Λ).filter br) label
                  = activity w a label + actSum w (Λ.filter br) label := by
                rw [List.filter_cons, if_pos hba, actSum_cons]
              rw [hact]
              exact Q'.le_trans' _ _ _ h4 h5
          | false =>
              -- XiB (a::Λ) ≃ XiB Λ + ζa·XiB qP' Λ
              --   ≤ aS·A + ζa·(aS·XiR qP') ≃ aS·(A + ζa·XiR qP')
              --   ≃ aS·XiR (a::Λ) = actSum'·XiR (a::Λ)
              have hbranch :=
                XiB_mapbranch_nobridge w qP br a Λ label hqa hba
              have hIH' := XiB_le_actSum_mul_XiR hw br label Λ
                (fun X => qP X && compatibleB a X)
              have h1 : XiB w qP br (a :: Λ) label
                  ≤ actSum w (Λ.filter br) label * XiR w qP Λ label
                    + activity w a label
                        * (actSum w (Λ.filter br) label
                            * XiR w (fun X => qP X && compatibleB a X) Λ label) := by
                refine Q'.le_trans' _ _ _
                  (Q'.le_of_eqv (XiB_cons w qP br a Λ label)) ?_
                refine Q'.add_le_add hIH ?_
                refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hbranch) ?_
                exact Q'.mul_le_mul_of_nonneg_left _ _ _ hIH' hζ
              -- ζa·(aS·X) ≃ aS·(ζa·X)
              have hswap : (activity w a label
                    * (actSum w (Λ.filter br) label
                        * XiR w (fun X => qP X && compatibleB a X) Λ label)).eqv
                  (actSum w (Λ.filter br) label
                    * (activity w a label
                        * XiR w (fun X => qP X && compatibleB a X) Λ label)) := by
                refine Q'.eqv_trans _ _ _
                  (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
                refine Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
                exact Q'.mul_assoc_eqv _ _ _
              have hfold : (actSum w (Λ.filter br) label * XiR w qP Λ label
                    + actSum w (Λ.filter br) label
                        * (activity w a label
                            * XiR w (fun X => qP X && compatibleB a X) Λ label)).eqv
                  (actSum w (Λ.filter br) label * XiR w qP (a :: Λ) label) := by
                refine Q'.eqv_trans _ _ _
                  (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
                exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hsplit)
              have hact : actSum w ((a :: Λ).filter br) label
                  = actSum w (Λ.filter br) label := by
                rw [List.filter_cons,
                  if_neg (by rw [hba]; exact Bool.false_ne_true)]
              rw [hact]
              refine Q'.le_trans' _ _ _ h1 ?_
              refine Q'.le_trans' _ _ _
                (Q'.add_le_add (Q'.le_refl' _) (Q'.le_of_eqv hswap)) ?_
              exact Q'.le_of_eqv hfold

/-! ## 4. The two-point instantiation -/

/-- The two-point bridge marker: `X` covers BOTH plaquettes `p` and `q`. -/
def coversBothB [DecidableEq L.Plaquette] (p q : L.Plaquette)
    (X : Polymer L) : Bool :=
  decide (p ∈ X) && decide (q ∈ X)

/-- **`XiBoth_le` (PROVED — the two-point single-bridge bound).**  The
compatible sub-families containing a polymer covering both `p` and `q` are
dominated by (the activity sum of the `p,q`-bridging polymers of `Γ`) times
the full partition sum.  This is the leading term of the two-point Mayer
expansion, with the bridging list `Γ.filter (coversBothB p q)` exactly the
carrier whose z4 size floor + KP domination were proved in
`LoopyPinnedPenroseUrsell`. -/
theorem XiBoth_le [DecidableEq L.Plaquette] {w : Q'} (hw : (0 : Q') ≤ w)
    (p q : L.Plaquette) (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (qP : Polymer L → Bool) :
    XiB w qP (coversBothB p q) Γ label
      ≤ actSum w (Γ.filter (coversBothB p q)) label * XiR w qP Γ label :=
  XiB_le_actSum_mul_XiR hw (coversBothB p q) label Γ qP

end YMGap.Continuum.XiPinnedBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.XiPinnedBridge.actSum_nonneg
#print axioms YMGap.Continuum.XiPinnedBridge.XiB_cons
#print axioms YMGap.Continuum.XiPinnedBridge.XiB_mapbranch_none
#print axioms YMGap.Continuum.XiPinnedBridge.XiB_mapbranch_bridge
#print axioms YMGap.Continuum.XiPinnedBridge.XiB_mapbranch_nobridge
#print axioms YMGap.Continuum.XiPinnedBridge.XiR_cons_split_true
#print axioms YMGap.Continuum.XiPinnedBridge.XiR_le_cons
#print axioms YMGap.Continuum.XiPinnedBridge.XiR_pred_mono
#print axioms YMGap.Continuum.XiPinnedBridge.actSum_filter_le_cons
#print axioms YMGap.Continuum.XiPinnedBridge.XiB_le_actSum_mul_XiR
#print axioms YMGap.Continuum.XiPinnedBridge.XiBoth_le
