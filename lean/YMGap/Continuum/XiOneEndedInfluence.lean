/-
# One-ended mixed-restriction influence

The unmarked-head branch of the double-avoidance induction requires control
of how a single avoidance partition changes when the tail is restricted to
polymers compatible with the head.  This file packages the two products in
that determinant, proves their exact cons expansions and nonnegativity, and
tests the head-rooted chain carrier on the first indirect influence path.

The test also refutes the direct-head-bridge envelope: a marker can influence
the head through one intermediate polymer even when no marked polymer meets
the head directly.  The fuel-bounded walk carrier contains the missing
two-edge term.  The global two-sided influence domination remains the next
induction lemma; it is not assumed here.
-/

import YMGap.Continuum.XiAvoidanceChainDomination

namespace YMGap.Continuum.XiOneEndedInfluence

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPinnedBridge
open YMGap.Continuum.XiChainBound
open YMGap.Continuum.XiSignLayer
open YMGap.Continuum.XiAvoidanceChainBound
open YMGap.Continuum.XiAvoidanceChainDomination

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- The add-one branch for a restricted partition function. -/
def xiBranch (w : Q') (q : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  if q a then
    activity w a label *
      XiR w (fun X => q X && compatibleB a X) Λ label
  else 0

/-- Uniform `if`-form of the exact `XiR` cons split. -/
theorem XiR_cons_split_if (w : Q') (q : Polymer L → Bool)
    (a : Polymer L) (Λ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    XiR w q (a :: Λ) label ≈
      XiR w q Λ label + xiBranch w q a Λ label := by
  cases hqa : q a with
  | true =>
      unfold xiBranch
      rw [if_pos hqa]
      exact XiR_cons_split_true w q a Λ label hqa
  | false =>
      unfold xiBranch
      rw [if_neg (fun h => Bool.false_ne_true (hqa.symm.trans h))]
      unfold XiR
      rw [sublists_cons, List.filter_append]
      refine Q'.eqv_trans _ _ _ (polySum_append w label _ _) ?_
      rw [XiR_cons_mapbranch_false q a Λ hqa, polySum_nil]
      exact Q'.eqv_refl _

/-- Pure four-term product expansion used by both mixed products. -/
theorem product_cons_expand (A A' B B' : Q') :
    (A + A') * (B + B') ≈
      A * B + (A * B' + A' * B) + A' * B' := by
  ring_qeqv

/-- Product of two independently restricted partition functions. -/
def restrictionPair (w : Q') (q r s : Polymer L → Bool)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  XiR w (fun X => q X && r X) Γ label *
    XiR w (fun X => q X && s X) Γ label

/-- Exact cons split of a restriction pair.  This is the algebraic shape
which creates the mixed cross term in the global induction. -/
theorem restrictionPair_cons_split (w : Q')
    (q r s : Polymer L → Bool) (a : Polymer L)
    (Λ : List (Polymer L)) (label : L.Plaquette → Rep) :
    restrictionPair w q r s (a :: Λ) label ≈
      restrictionPair w q r s Λ label +
        (XiR w (fun X => q X && r X) Λ label *
            xiBranch w (fun X => q X && s X) a Λ label +
          xiBranch w (fun X => q X && r X) a Λ label *
            XiR w (fun X => q X && s X) Λ label) +
        xiBranch w (fun X => q X && r X) a Λ label *
          xiBranch w (fun X => q X && s X) a Λ label := by
  unfold restrictionPair
  have hr := XiR_cons_split_if w (fun X => q X && r X) a Λ label
  have hs := XiR_cons_split_if w (fun X => q X && s X) a Λ label
  exact Q'.eqv_trans _ _ _ (mul_eqv_congr_both hr hs)
    (product_cons_expand _ _ _ _)

/-- Product `Av_q(b) · XiR(q∧compatible(head))`. -/
def oneEndedLeft (w : Q') (q b : Polymer L → Bool) (head : Polymer L)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  restrictionPair w q (fun X => !(b X))
    (fun X => compatibleB head X) Γ label

/-- Product `Av_{q∧compatible(head)}(b) · XiR(q)`. -/
def oneEndedRight (w : Q') (q b : Polymer L → Bool) (head : Polymer L)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) : Q' :=
  restrictionPair w q
    (fun X => !(b X) && compatibleB head X) (fun _ => true) Γ label

/-- The head-rooted connecting-walk carrier: start at a `b`-marked polymer
and terminate at a polymer incompatible with the external head. -/
def oneEndedInfluenceCarrier (w : Q') (q b : Polymer L → Bool)
    (head : Polymer L) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) : Q' :=
  connectingChainMajorant w q b (fun X => !(compatibleB head X)) Γ label

theorem restrictionPair_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (q r s : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    (0 : Q') ≤ restrictionPair w q r s Γ label := by
  unfold restrictionPair
  exact Q'.mul_nonneg _ _ (XiR_nonneg hw _ Γ label)
    (XiR_nonneg hw _ Γ label)

theorem oneEndedLeft_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (q b : Polymer L → Bool) (head : Polymer L)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ oneEndedLeft w q b head Γ label :=
  restrictionPair_nonnegative hw _ _ _ Γ label

theorem oneEndedRight_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    (q b : Polymer L → Bool) (head : Polymer L)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ oneEndedRight w q b head Γ label :=
  restrictionPair_nonnegative hw _ _ _ Γ label

theorem oneEndedInfluenceCarrier_nonnegative {w : Q'}
    (hw : (0 : Q') ≤ w) (q b : Polymer L → Bool) (head : Polymer L)
    (Γ : List (Polymer L)) (label : L.Plaquette → Rep) :
    (0 : Q') ≤ oneEndedInfluenceCarrier w q b head Γ label :=
  connectingChainMajorant_nonnegative hw q b
    (fun X => !(compatibleB head X)) Γ label

/-! ## The first indirect one-ended influence -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def p2 : TL.Plaquette := (2, 0)
private def X : Polymer TL := [p0]
private def Y : Polymer TL := [p0, p1]
private def head : Polymer TL := [p1, p2]
private def Γ : List (Polymer TL) := [X, Y]
private def qAll : Polymer TL → Bool := fun _ => true
private def markX : Polymer TL → Bool := fun T => decide (T = X)
private def label0 : TL.Plaquette → Rep := fun _ => 0

/-- There is no direct polymer carrying `markX` and meeting the head. -/
theorem indirect_head_path_has_no_direct_bridge :
    bareDirectChainCarrier 1 qAll markX
      (fun T => !(compatibleB head T)) Γ label0 ≈ (0 : Q') := by
  unfold bareDirectChainCarrier Γ qAll markX head X Y p0 p1 p2 label0
    compatibleB actSum activity plaqWeight coeffW dimQ c4 qpow
  decide

/-- Exact one-ended determinant on `X -- Y -- head`: the direct envelope
fails because `oneEndedLeft = 4` and `oneEndedRight = 3`. -/
theorem direct_one_ended_influence_envelope_fails :
    ¬ (oneEndedLeft 1 qAll markX head Γ label0 ≤
      oneEndedRight 1 qAll markX head Γ label0 +
        bareDirectChainCarrier 1 qAll markX
          (fun T => !(compatibleB head T)) Γ label0 *
            XiR 1 qAll Γ label0) := by
  unfold oneEndedLeft oneEndedRight restrictionPair bareDirectChainCarrier
    Γ qAll markX head X Y p0 p1 p2 label0 XiR compatibleB actSum
    polySum familyCompatibleB familyActivity activity plaqWeight coeffW dimQ
    c4 qpow sublists
  decide

/-- The head-rooted all-walk carrier contains the missing two-edge path and
repairs the exact one-ended determinant. -/
theorem head_rooted_walk_repairs_indirect_influence :
    oneEndedLeft 1 qAll markX head Γ label0 ≤
      oneEndedRight 1 qAll markX head Γ label0 +
        oneEndedInfluenceCarrier 1 qAll markX head Γ label0 *
          XiR 1 qAll Γ label0 := by
  unfold oneEndedLeft oneEndedRight restrictionPair
    oneEndedInfluenceCarrier connectingChainMajorant chainWalkFrom
    chainWalkTerminal polymerWeightedSum Γ qAll markX head X Y p0 p1 p2
    label0 XiR compatibleB polySum familyCompatibleB familyActivity activity
    plaqWeight coeffW dimQ c4 qpow sublists
  decide

#print axioms XiR_cons_split_if
#print axioms product_cons_expand
#print axioms restrictionPair_cons_split
#print axioms restrictionPair_nonnegative
#print axioms oneEndedLeft_nonnegative
#print axioms oneEndedRight_nonnegative
#print axioms oneEndedInfluenceCarrier_nonnegative
#print axioms indirect_head_path_has_no_direct_bridge
#print axioms direct_one_ended_influence_envelope_fails
#print axioms head_rooted_walk_repairs_indirect_influence

end YMGap.Continuum.XiOneEndedInfluence
