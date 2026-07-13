/-
# Double-avoidance chain domination: induction diagnostics

This successor to `XiAvoidanceChainBound` audits the repeated-walk carrier
needed by the global cons induction.  The carrier is monotone in its fuel,
so additional cons fuel cannot remove a previously available chain.

The direct expansion of an unmarked head nevertheless contains a mixed
restriction cross term.  A fully computed three-polymer path proves that
dropping this term is false: the two tail endpoints are compatible, but the
head joins them by two incompatibility edges and contributes exactly one.
This file banks that obstruction and its exact head-chain repair.  It does
not assert the still-open all-list domination.
-/

import YMGap.Continuum.XiAvoidanceChainBound

namespace YMGap.Continuum.XiAvoidanceChainDomination

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPinnedBridge
open YMGap.Continuum.XiChainBound
open YMGap.Continuum.XiSignLayer
open YMGap.Continuum.XiAvoidanceChainBound

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

omit [DecidableEq L.Plaquette] in
theorem polymerWeightedSum_mono
    {F G : Polymer L → Q'} (hFG : ∀ X : Polymer L, F X ≤ G X) :
    ∀ Γ : List (Polymer L),
      polymerWeightedSum F Γ ≤ polymerWeightedSum G Γ
  | [] => Q'.le_refl' _
  | X :: Γ =>
      Q'.add_le_add (hFG X) (polymerWeightedSum_mono hFG Γ)

/-- Repeated-walk fuel is genuinely nested: every walk available with
`fuel` remains available with `fuel+1`. -/
theorem chainWalkFrom_fuel_mono {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) :
    ∀ (fuel : Nat) (bg : Polymer L → Bool) (X : Polymer L),
      chainWalkFrom w qP b2 Γ label fuel bg X ≤
        chainWalkFrom w qP b2 Γ label (fuel + 1) bg X
  | 0, bg, X => by
      unfold chainWalkFrom
      apply Q'.add_le_self_of_nonneg
      exact Q'.mul_nonneg _ _ (activity_nonneg hw X label)
        (polymerWeightedSum_nonnegative _ (fun Y => by
          split
          · exact chainWalkFrom_nonnegative hw qP b2 Γ label 0
              (fun T => bg T && compatibleB X T) Y
          · exact Q'.le_refl' _) Γ)
  | fuel + 1, bg, X => by
      unfold chainWalkFrom
      apply Q'.add_le_add
      · exact Q'.le_refl' _
      · apply Q'.mul_le_mul_of_nonneg_left
        · apply polymerWeightedSum_mono
          intro Y
          split
          · exact chainWalkFrom_fuel_mono hw qP b2 Γ label fuel
              (fun T => bg T && compatibleB X T) Y
          · exact Q'.le_refl' _
        · exact activity_nonneg hw X label

/-- Monotonicity for any finite fuel extension. -/
theorem chainWalkFrom_fuel_add_mono {w : Q'} (hw : (0 : Q') ≤ w)
    (qP b2 : Polymer L → Bool) (Γ : List (Polymer L))
    (label : L.Plaquette → Rep) (fuel : Nat)
    (bg : Polymer L → Bool) (X : Polymer L) :
    ∀ d : Nat,
      chainWalkFrom w qP b2 Γ label fuel bg X ≤
        chainWalkFrom w qP b2 Γ label (fuel + d) bg X
  | 0 => by simp only [Nat.add_zero]; exact Q'.le_refl' _
  | d + 1 => by
      exact Q'.le_trans' _ _ _
        (chainWalkFrom_fuel_add_mono hw qP b2 Γ label fuel bg X d)
        (by
          rw [show fuel + (d + 1) = (fuel + d) + 1 by omega]
          exact chainWalkFrom_fuel_mono hw qP b2 Γ label (fuel + d) bg X)

/-! ## Exact obstruction to the naive mixed-restriction branch -/

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance
private def px : TL.Plaquette := (0, 0)
private def pz : TL.Plaquette := (1, 0)
private def X : Polymer TL := [px]
private def H : Polymer TL := [px, pz]
private def Z : Polymer TL := [pz]
private def endpoints : List (Polymer TL) := [X, Z]
private def qAll : Polymer TL → Bool := fun _ => true
private def qHeadCompatible : Polymer TL → Bool :=
  fun T => compatibleB H T
private def markX : Polymer TL → Bool := fun T => decide (T = X)
private def markZ : Polymer TL → Bool := fun T => decide (T = Z)
private def label0 : TL.Plaquette → Rep := fun _ => 0

/-- Naively pairing the two mixed restriction terms against the two
single-avoidance terms fails: the exact comparison is `5 ≤ 4`. -/
theorem naive_mixed_restriction_cross_fails :
    ¬ (cellA 1 qAll markX markZ endpoints label0 *
          XiR 1 qHeadCompatible endpoints label0 +
        cellA 1 qHeadCompatible markX markZ endpoints label0 *
          XiR 1 qAll endpoints label0 ≤
      XiAvoid 1 qAll markX endpoints label0 *
          XiAvoid 1 qHeadCompatible markZ endpoints label0 +
        XiAvoid 1 qHeadCompatible markX endpoints label0 *
          XiAvoid 1 qAll markZ endpoints label0) := by
  unfold cellA XiAvoid XiR endpoints qAll qHeadCompatible markX markZ H X Z
    px pz label0 familyCompatibleB compatibleB polySum familyActivity activity
    plaqWeight coeffW dimQ c4 qpow sublists
  decide

/-- The head-mediated two-edge chain has exact unit weight and repairs the
mixed restriction comparison (`5 ≤ 4+1`). -/
theorem mixed_restriction_cross_repaired_by_head_chain :
    cellA 1 qAll markX markZ endpoints label0 *
          XiR 1 qHeadCompatible endpoints label0 +
        cellA 1 qHeadCompatible markX markZ endpoints label0 *
          XiR 1 qAll endpoints label0 ≤
      XiAvoid 1 qAll markX endpoints label0 *
          XiAvoid 1 qHeadCompatible markZ endpoints label0 +
        XiAvoid 1 qHeadCompatible markX endpoints label0 *
          XiAvoid 1 qAll markZ endpoints label0 +
        activity 1 X label0 * activity 1 H label0 * activity 1 Z label0 := by
  unfold cellA XiAvoid XiR endpoints qAll qHeadCompatible markX markZ H X Z
    px pz label0 familyCompatibleB compatibleB polySum familyActivity activity
    plaqWeight coeffW dimQ c4 qpow sublists
  decide

#print axioms polymerWeightedSum_mono
#print axioms chainWalkFrom_fuel_mono
#print axioms chainWalkFrom_fuel_add_mono
#print axioms naive_mixed_restriction_cross_fails
#print axioms mixed_restriction_cross_repaired_by_head_chain

end YMGap.Continuum.XiAvoidanceChainDomination
