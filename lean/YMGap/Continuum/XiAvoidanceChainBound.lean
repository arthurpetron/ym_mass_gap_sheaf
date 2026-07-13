/-
# Double-avoidance excess: cons splits and the first connecting chain

This independent polymer-gas lane opens the finite-volume induction behind
the remaining sign inequality in `XiSignLayer`.  It supplies exact `XiR`
representations and cons splits for the single- and double-avoidance sums,
then tests the direct (one-polymer) chain envelope on the smallest lists.

The direct envelope survives one and two polymers, but fails on the first
genuine incompatibility chain of three polymers.  The failure is banked on a
fully computed hard-core gas with unit activities.  The missing unit is
exactly the product along the two-edge chain, and the corrected chain stratum
repairs that instance.  This is a checked fence and an induction substrate;
it is not yet the all-length connecting-chain domination.
-/

import YMGap.Continuum.XiSignLayer

namespace YMGap.Continuum.XiAvoidanceChainBound

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPinnedBridge
open YMGap.Continuum.XiChainBound
open YMGap.Continuum.XiSignLayer

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

/-! ## Avoidance sums as restricted partition functions -/

omit [DecidableEq L.Plaquette] in
/-- Boolean De Morgan law for finite-list markers. -/
private theorem all_not_eq_not_any (b : Polymer L → Bool) :
    ∀ S : List (Polymer L),
      S.all (fun X => !(b X)) = !(S.any b)
  | [] => rfl
  | X :: S => by
      rw [List.all_cons, List.any_cons, all_not_eq_not_any b S]
      cases b X <;> cases S.any b <;> rfl

/-- Single avoidance is exactly `XiR` with the marker excluded in the
per-polymer predicate. -/
theorem XiAvoid_eqv_XiR (w : Q') (qP b : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    XiAvoid w qP b Γ label ≈
      XiR w (fun X => qP X && !(b X)) Γ label := by
  unfold XiAvoid XiR
  refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
  apply List.filter_congr
  intro S _hS
  rw [← all_and qP (fun X => !(b X)) S]
  rw [all_not_eq_not_any b S]
  cases S.all qP <;> cases S.all (fun X => !(b X)) <;>
    cases S.any b <;> cases familyCompatibleB S <;> rfl

/-- Double avoidance is exactly `XiR` with both markers excluded. -/
theorem cellA_eqv_XiR (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    cellA w qP b1 b2 Γ label ≈
      XiR w (fun X => (qP X && !(b1 X)) && !(b2 X)) Γ label := by
  unfold cellA XiR
  refine Q'.eqv_of_eq (congrArg (polySum w label) ?_)
  apply List.filter_congr
  intro S _hS
  rw [← all_and (fun X => qP X && !(b1 X)) (fun X => !(b2 X)) S,
    ← all_and qP (fun X => !(b1 X)) S]
  rw [all_not_eq_not_any b1 S, all_not_eq_not_any b2 S]
  cases S.all qP <;> cases S.all (fun X => !(b1 X)) <;>
    cases S.all (fun X => !(b2 X)) <;> cases S.any b1 <;>
    cases S.any b2 <;> cases familyCompatibleB S <;> rfl

/-- Constructive cons split for single avoidance.  A head contributes exactly
when it passes `qP` and avoids the marker; its tail predicate is strengthened
by hard-core compatibility with that head. -/
theorem XiAvoid_cons_split (w : Q') (qP b : Polymer L → Bool)
    (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiAvoid w qP b (a :: Λ) label ≈
      XiAvoid w qP b Λ label +
        (if qP a && !(b a) then
          activity w a label *
            XiR w (fun X => (qP X && !(b X)) && compatibleB a X) Λ label
        else 0) := by
  have hhead : (qP a && !(b a)) = true ∨
      (qP a && !(b a)) = false := by
    cases qP a <;> cases b a <;> simp
  cases hhead with
  | inl htrue =>
      rw [if_pos htrue]
      refine Q'.eqv_trans _ _ _ (XiAvoid_eqv_XiR w qP b (a :: Λ) label) ?_
      refine Q'.eqv_trans _ _ _
        (XiR_cons_split_true w (fun X => qP X && !(b X)) a Λ label htrue) ?_
      exact add_eqv_congr_both _ _ _ _
        (Q'.eqv_symm (XiAvoid_eqv_XiR w qP b Λ label)) (Q'.eqv_refl _)
  | inr hfalse =>
      rw [if_neg (fun h => Bool.false_ne_true (hfalse.symm.trans h))]
      refine Q'.eqv_trans _ _ _ (XiAvoid_eqv_XiR w qP b (a :: Λ) label) ?_
      have hraw : XiR w (fun X => qP X && !(b X)) (a :: Λ) label ≈
          XiR w (fun X => qP X && !(b X)) Λ label := by
        unfold XiR
        rw [sublists_cons, List.filter_append]
        refine Q'.eqv_trans _ _ _ (polySum_append w label _ _) ?_
        rw [XiR_cons_mapbranch_false (fun X => qP X && !(b X)) a Λ hfalse,
          polySum_nil]
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      refine Q'.eqv_trans _ _ _ hraw ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (XiAvoid_eqv_XiR w qP b Λ label)) ?_
      exact Q'.eqv_symm (QPoly.q_add_zero_eqv _)

/-- Constructive cons split for the double-avoidance cell. -/
theorem cellA_cons_split (w : Q') (qP b1 b2 : Polymer L → Bool)
    (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    cellA w qP b1 b2 (a :: Λ) label ≈
      cellA w qP b1 b2 Λ label +
        (if (qP a && !(b1 a)) && !(b2 a) then
          activity w a label * XiR w
            (fun X => ((qP X && !(b1 X)) && !(b2 X)) && compatibleB a X)
            Λ label
        else 0) := by
  have hhead : ((qP a && !(b1 a)) && !(b2 a)) = true ∨
      ((qP a && !(b1 a)) && !(b2 a)) = false := by
    cases qP a <;> cases b1 a <;> cases b2 a <;> simp
  cases hhead with
  | inl htrue =>
      rw [if_pos htrue]
      refine Q'.eqv_trans _ _ _
        (cellA_eqv_XiR w qP b1 b2 (a :: Λ) label) ?_
      refine Q'.eqv_trans _ _ _
        (XiR_cons_split_true w
          (fun X => (qP X && !(b1 X)) && !(b2 X)) a Λ label htrue) ?_
      exact add_eqv_congr_both _ _ _ _
        (Q'.eqv_symm (cellA_eqv_XiR w qP b1 b2 Λ label))
        (Q'.eqv_refl _)
  | inr hfalse =>
      rw [if_neg (fun h => Bool.false_ne_true (hfalse.symm.trans h))]
      refine Q'.eqv_trans _ _ _
        (cellA_eqv_XiR w qP b1 b2 (a :: Λ) label) ?_
      have hraw :
          XiR w (fun X => (qP X && !(b1 X)) && !(b2 X)) (a :: Λ) label ≈
            XiR w (fun X => (qP X && !(b1 X)) && !(b2 X)) Λ label := by
        unfold XiR
        rw [sublists_cons, List.filter_append]
        refine Q'.eqv_trans _ _ _ (polySum_append w label _ _) ?_
        rw [XiR_cons_mapbranch_false
          (fun X => (qP X && !(b1 X)) && !(b2 X)) a Λ hfalse,
          polySum_nil]
        exact Q'.eqv_of_eq (Q'.add_zero' _)
      refine Q'.eqv_trans _ _ _ hraw ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (cellA_eqv_XiR w qP b1 b2 Λ label)) ?_
      exact Q'.eqv_symm (QPoly.q_add_zero_eqv _)

/-! ## The direct and two-edge chain strata -/

/-- Bare same-polymer bridge activity.  This is the tempting undressed
length-one envelope tested below; it does not yet retain a compatible
background partition factor. -/
def bareDirectChainCarrier (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  actSum w (Γ.filter (fun X => (qP X && b1 X) && b2 X)) label

/-- A finite weighted sum over a polymer list, with no compatibility filter.
It is the substrate for clusters, whose members are allowed (and required)
to be mutually incompatible along selected edges. -/
def polymerWeightedSum (F : Polymer L → Q') : List (Polymer L) → Q'
  | [] => 0
  | X :: Γ => F X + polymerWeightedSum F Γ

omit [DecidableEq L.Plaquette] in
/-- Weighted list sums preserve nonnegativity. -/
theorem polymerWeightedSum_nonnegative
    (F : Polymer L → Q')
    (hF : ∀ X : Polymer L, (0 : Q') ≤ F X) :
    ∀ Γ : List (Polymer L), (0 : Q') ≤ polymerWeightedSum F Γ
  | [] => Q'.le_refl' _
  | X :: Γ =>
      Q'.zero_le_add _ _ (hF X) (polymerWeightedSum_nonnegative F hF Γ)

/-- The correctly dressed direct-chain stratum: each shared-marker polymer
is paired with the partition sum of the background compatible with it. -/
def dressedDirectChainCarrier (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polymerWeightedSum (fun X =>
    if (qP X && b1 X) && b2 X then
      activity w X label *
        XiR w (fun T => qP T && compatibleB X T) Γ label
    else 0) Γ

/-- Activity sum of all ordered two-edge incompatibility chains
`X -- Y -- Z` with the endpoint markers, dressed by the partition sum of
the background compatible with every chain member.  Repetitions are
deliberately allowed; this is an upper-envelope stratum and hence remains
subtraction free. -/
def dressedTwoEdgeChainCarrier (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polymerWeightedSum (fun X =>
    if qP X && b1 X then
      activity w X label * polymerWeightedSum (fun Y =>
        if qP Y && !(compatibleB X Y) then
          activity w Y label * polymerWeightedSum (fun Z =>
            if (qP Z && b2 Z) && !(compatibleB Y Z) then
              activity w Z label * XiR w
                (fun T => (((qP T && compatibleB X T) && compatibleB Y T)
                  && compatibleB Z T)) Γ label
            else 0) Γ
        else 0) Γ
    else 0) Γ

/-- The dressed direct-chain stratum is manifestly nonnegative. -/
theorem dressedDirectChainCarrier_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    (0 : Q') ≤ dressedDirectChainCarrier w qP b1 b2 Γ label := by
  unfold dressedDirectChainCarrier
  apply polymerWeightedSum_nonnegative
  intro X
  split
  · exact Q'.mul_nonneg _ _ (activity_nonneg hw X label)
      (XiR_nonneg hw _ Γ label)
  · exact Q'.le_refl' _

/-- The dressed two-edge chain stratum is manifestly nonnegative. -/
theorem dressedTwoEdgeChainCarrier_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    (0 : Q') ≤ dressedTwoEdgeChainCarrier w qP b1 b2 Γ label := by
  unfold dressedTwoEdgeChainCarrier
  apply polymerWeightedSum_nonnegative
  intro X
  split
  · apply Q'.mul_nonneg
    · exact activity_nonneg hw X label
    · apply polymerWeightedSum_nonnegative
      intro Y
      split
      · apply Q'.mul_nonneg
        · exact activity_nonneg hw Y label
        · apply polymerWeightedSum_nonnegative
          intro Z
          split
          · exact Q'.mul_nonneg _ _ (activity_nonneg hw Z label)
              (XiR_nonneg hw _ Γ label)
          · exact Q'.le_refl' _
      · exact Q'.le_refl' _
  · exact Q'.le_refl' _

/-- Terminal weight of a connecting walk.  The endpoint must carry the
second marker, and the compatible background predicate accumulated along
the walk is intersected once more with the endpoint compatibility test. -/
def chainWalkTerminal (w : Q') (qP b2 bg : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep)
    (X : Polymer L) : Q' :=
  if qP X && b2 X then
    activity w X label *
      XiR w (fun T => (qP T && bg T) && compatibleB X T) Γ label
  else 0

/-- Fuel-bounded incompatibility walk from a current polymer to a
`b2`-marked endpoint.  Each extension multiplies by the current activity,
chooses an incompatible next polymer, and strengthens the background by
compatibility with the current polymer.  The construction uses additions,
products and filters only. -/
def chainWalkFrom (w : Q') (qP b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    Nat → (Polymer L → Bool) → Polymer L → Q'
  | 0, bg, X => chainWalkTerminal w qP b2 bg Γ label X
  | fuel + 1, bg, X =>
      chainWalkTerminal w qP b2 bg Γ label X +
        activity w X label * polymerWeightedSum (fun Y =>
          if qP Y && !(compatibleB X Y) then
            chainWalkFrom w qP b2 Γ label fuel
              (fun T => bg T && compatibleB X T) Y
          else 0) Γ

/-- Explicit all-length connecting-chain majorant.  Fuel is the number of
available polymers; repeated walks are allowed, making this a genuine upper
envelope rather than a simple-path equality. -/
def connectingChainMajorant (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  polymerWeightedSum (fun X =>
    if qP X && b1 X then
      chainWalkFrom w qP b2 Γ label Γ.length (fun _ => true) X
    else 0) Γ

theorem chainWalkTerminal_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 bg : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (X : Polymer L) :
    (0 : Q') ≤ chainWalkTerminal w qP b2 bg Γ label X := by
  unfold chainWalkTerminal
  split
  · exact Q'.mul_nonneg _ _ (activity_nonneg hw X label)
      (XiR_nonneg hw _ Γ label)
  · exact Q'.le_refl' _

theorem chainWalkFrom_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    ∀ (fuel : Nat) (bg : Polymer L → Bool) (X : Polymer L),
      (0 : Q') ≤ chainWalkFrom w qP b2 Γ label fuel bg X
  | 0, bg, X => chainWalkTerminal_nonnegative hw qP b2 bg Γ label X
  | fuel + 1, bg, X => by
      unfold chainWalkFrom
      apply Q'.zero_le_add
      · exact chainWalkTerminal_nonnegative hw qP b2 bg Γ label X
      · apply Q'.mul_nonneg
        · exact activity_nonneg hw X label
        · apply polymerWeightedSum_nonnegative
          intro Y
          split
          · exact chainWalkFrom_nonnegative hw qP b2 Γ label fuel
              (fun T => bg T && compatibleB X T) Y
          · exact Q'.le_refl' _

theorem connectingChainMajorant_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b1 b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    (0 : Q') ≤ connectingChainMajorant w qP b1 b2 Γ label := by
  unfold connectingChainMajorant
  apply polymerWeightedSum_nonnegative
  intro X
  split
  · exact chainWalkFrom_nonnegative hw qP b2 Γ label Γ.length
      (fun _ => true) X
  · exact Q'.le_refl' _

/-- The first corrected chain envelope contains both the direct stratum and
the first positive (two-incompatibility-edge) stratum. -/
def firstChainCarrier (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  dressedDirectChainCarrier w qP b1 b2 Γ label +
    dressedTwoEdgeChainCarrier w qP b1 b2 Γ label

private theorem le_of_add_le_add_right {a b c : Q'}
    (h : a + c ≤ b + c) : a ≤ b := by
  have h' := Q'.add_le_add_right _ _ (-c) h
  have ha : (a + c) + -c ≈ a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a c (-c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have hb : (b + c) + -c ≈ b := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b c (-c)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' b)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm ha))
    (Q'.le_trans' _ _ _ h' (Q'.le_of_eqv hb))

/-- Any subtraction-free avoidance-chain bound plugs directly into the exact
Mayer identity and yields the corresponding truncated-numerator bound.  The
common avoidance product is cancelled only after all terms have remained
nonnegative. -/
theorem truncated_numerator_le_of_avoidance_chain
    (w : Q') (qP b1 b2 : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) (C : Q')
    (havoid :
      cellA w qP b1 b2 Γ label * XiR w qP Γ label ≤
        XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label +
          C * XiR w qP Γ label) :
    XiB2 w qP b1 b2 Γ label * XiR w qP Γ label ≤
      XiB w qP b1 Γ label * XiB w qP b2 Γ label +
        C * XiR w qP Γ label := by
  have hm := two_point_mayer w qP b1 b2 Γ label
  have hM := Q'.le_of_eqv hm
  have hP := Q'.add_le_add_left
    (XiB w qP b1 Γ label * XiB w qP b2 Γ label) _ _ havoid
  have hchain := Q'.le_trans' _ _ _ hM hP
  have hre :
      XiB w qP b1 Γ label * XiB w qP b2 Γ label +
          (XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label +
            C * XiR w qP Γ label) ≈
        (XiB w qP b1 Γ label * XiB w qP b2 Γ label +
            C * XiR w qP Γ label) +
          XiAvoid w qP b1 Γ label * XiAvoid w qP b2 Γ label := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
    exact swap_mid _ _ _
  apply le_of_add_le_add_right
  exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv hre)

/-! ## Exact finite tests and the minimal direct-envelope no-go -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def px : TL.Plaquette := (0, 0)
private def pz : TL.Plaquette := (1, 0)
private def X : Polymer TL := [px]
private def Y : Polymer TL := [px, pz]
private def Z : Polymer TL := [pz]
private def Γone : List (Polymer TL) := [X]
private def Γtwo : List (Polymer TL) := [X, Z]
private def Γpath : List (Polymer TL) := [X, Y, Z]
private def qAll : Polymer TL → Bool := fun _ => true
private def markX : Polymer TL → Bool := fun T => decide (T = X)
private def markZ : Polymer TL → Bool := fun T => decide (T = Z)
private def label0 : TL.Plaquette → Rep := fun _ => 0

/-- One-polymer exact test: the direct carrier pays the complete avoidance
excess when the sole polymer carries both endpoint marks. -/
theorem one_polymer_direct_chain_test :
    cellA 1 qAll markX markX Γone label0 * XiR 1 qAll Γone label0 ≤
      XiAvoid 1 qAll markX Γone label0 * XiAvoid 1 qAll markX Γone label0 +
        bareDirectChainCarrier 1 qAll markX markX Γone label0 *
          XiR 1 qAll Γone label0 := by
  unfold cellA XiAvoid XiR bareDirectChainCarrier Γone qAll markX X px label0
    actSum familyCompatibleB compatibleB activity plaqWeight coeffW dimQ
    c4 qpow polySum familyActivity sublists
  decide

/-- Two-polymer exact test: two compatible, separately marked polymers have
zero avoidance excess, so no two-edge chain payment is needed. -/
theorem two_polymer_direct_chain_test :
    cellA 1 qAll markX markZ Γtwo label0 * XiR 1 qAll Γtwo label0 ≤
      XiAvoid 1 qAll markX Γtwo label0 * XiAvoid 1 qAll markZ Γtwo label0 +
        bareDirectChainCarrier 1 qAll markX markZ Γtwo label0 *
          XiR 1 qAll Γtwo label0 := by
  unfold cellA XiAvoid XiR bareDirectChainCarrier Γtwo qAll markX markZ X Z px pz
    label0 actSum familyCompatibleB compatibleB activity plaqWeight coeffW
    dimQ c4 qpow polySum familyActivity sublists
  decide

/-- Exact left side of the three-polymer path fence. -/
theorem three_path_double_avoidance_product_eqv_ten :
    cellA 1 qAll markX markZ Γpath label0 * XiR 1 qAll Γpath label0 ≈
      (10 : Q') := by
  unfold cellA XiR Γpath qAll markX markZ X Y Z px pz label0
    familyCompatibleB compatibleB polySum familyActivity activity plaqWeight
    coeffW dimQ c4 qpow sublists
  decide

/-- Exact product of the two single-avoidance sums on the path fence. -/
theorem three_path_single_avoidance_product_eqv_nine :
    XiAvoid 1 qAll markX Γpath label0 * XiAvoid 1 qAll markZ Γpath label0 ≈
      (9 : Q') := by
  unfold XiAvoid Γpath qAll markX markZ X Y Z px pz label0
    familyCompatibleB compatibleB polySum familyActivity activity plaqWeight
    coeffW dimQ c4 qpow sublists
  decide

/-- There is no shared-marker polymer on the three-polymer path. -/
theorem three_path_bare_direct_chain_eqv_zero :
    bareDirectChainCarrier 1 qAll markX markZ Γpath label0 ≈ (0 : Q') := by
  unfold bareDirectChainCarrier Γpath qAll markX markZ X Y Z px pz label0
    actSum activity plaqWeight coeffW dimQ c4 qpow
  decide

/-- The corrected dressed two-edge stratum is exactly the missing unit. -/
theorem three_path_dressed_two_edge_chain_eqv_one :
    dressedTwoEdgeChainCarrier 1 qAll markX markZ Γpath label0 ≈ (1 : Q') := by
  unfold dressedTwoEdgeChainCarrier
  unfold XiR Γpath qAll markX markZ X Y Z px pz label0
    familyCompatibleB compatibleB activity plaqWeight coeffW dimQ c4 qpow
    polySum familyActivity sublists polymerWeightedSum
  decide

/-- The smallest positive indirect excess: on the incompatibility path
`X -- Y -- Z`, the direct shared-marker carrier is zero while
`cellA·XiR = 10` and `XiAvoid(b1)·XiAvoid(b2) = 9`. -/
theorem direct_chain_envelope_fails_on_three_polymer_path :
    ¬ (cellA 1 qAll markX markZ Γpath label0 * XiR 1 qAll Γpath label0 ≤
      XiAvoid 1 qAll markX Γpath label0 * XiAvoid 1 qAll markZ Γpath label0 +
        bareDirectChainCarrier 1 qAll markX markZ Γpath label0 *
          XiR 1 qAll Γpath label0) := by
  unfold cellA XiAvoid XiR bareDirectChainCarrier Γpath qAll markX markZ X Y Z
    px pz label0 actSum familyCompatibleB compatibleB activity plaqWeight
    coeffW dimQ c4 qpow polySum familyActivity sublists
  decide

/-- The explicit two-edge chain stratum repairs the minimal counterexample,
without any subtraction or measured constant. -/
theorem first_chain_carrier_repairs_three_polymer_path :
    cellA 1 qAll markX markZ Γpath label0 * XiR 1 qAll Γpath label0 ≤
      XiAvoid 1 qAll markX Γpath label0 * XiAvoid 1 qAll markZ Γpath label0 +
        firstChainCarrier 1 qAll markX markZ Γpath label0 *
          XiR 1 qAll Γpath label0 := by
  unfold cellA XiAvoid firstChainCarrier dressedDirectChainCarrier
    dressedTwoEdgeChainCarrier
  unfold XiR Γpath qAll markX markZ X Y Z px pz label0
    familyCompatibleB compatibleB activity plaqWeight coeffW dimQ c4
    qpow polySum familyActivity sublists polymerWeightedSum
  decide

#print axioms XiAvoid_eqv_XiR
#print axioms cellA_eqv_XiR
#print axioms XiAvoid_cons_split
#print axioms cellA_cons_split
#print axioms polymerWeightedSum_nonnegative
#print axioms dressedDirectChainCarrier_nonnegative
#print axioms dressedTwoEdgeChainCarrier_nonnegative
#print axioms chainWalkTerminal_nonnegative
#print axioms chainWalkFrom_nonnegative
#print axioms connectingChainMajorant_nonnegative
#print axioms truncated_numerator_le_of_avoidance_chain
#print axioms one_polymer_direct_chain_test
#print axioms two_polymer_direct_chain_test
#print axioms three_path_double_avoidance_product_eqv_ten
#print axioms three_path_single_avoidance_product_eqv_nine
#print axioms three_path_bare_direct_chain_eqv_zero
#print axioms three_path_dressed_two_edge_chain_eqv_one
#print axioms direct_chain_envelope_fails_on_three_polymer_path
#print axioms first_chain_carrier_repairs_three_polymer_path

end YMGap.Continuum.XiAvoidanceChainBound
