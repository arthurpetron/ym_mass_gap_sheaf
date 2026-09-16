/-
# Computed eventual norm ceilings on the original reflected Cauchy carrier

Every physical intrinsic presentation has the previously computed uniform
probe cap. A Cauchy representative supplies its own anchor at modulus 1.
The actual reflected squared-sum inequality and cancellation inside the
pairing then give the explicit eventual ceiling 2+2*C_anchor.

No equality of signed-list presentations is asserted, and no norm bound is
assumed. The action, reflected form, spatial width and heat stage are the
same as those defining the existing seminorm. Pairing continuity and its
completed inner-product limit are subsequent consumers, not dependencies.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap

/-- The exact coefficient cap of the original reflected diagonal. -/
def diagonalCeiling (width : Nat) (x : PhysicalSpan width) : Q' :=
  uniformCap width x.val x.val

theorem diagonalCeiling_nonnegative (width : Nat) (x : PhysicalSpan width) :
    (0 : Q') ≤ diagonalCeiling width x :=
  uniformCap_nonnegative width x.val x.val

theorem diagonal_le_ceiling {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x : PhysicalSpan width) :
    leEv (pairing hw0 hw1 width x.val x.val stage) (ofQ' (diagonalCeiling width x)) :=
  (pairing_bounds hw0 hw1 width x.val x.val stage).2

/-- The anchor index is data already supplied by the actual Cauchy representative. -/
def normBase {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (X : (seminorm hw0 hw1 width stage).Cauchy) : Nat :=
  X.modulus 1

/-- A computed eventual diagonal ceiling, with no new boundedness premise. -/
def normCeiling {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (X : (seminorm hw0 hw1 width stage).Cauchy) : Q' :=
  (1+1) +
    (diagonalCeiling width (X.seq (normBase hw0 hw1 width stage X)) +
      diagonalCeiling width (X.seq (normBase hw0 hw1 width stage X)))

theorem normCeiling_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (X : (seminorm hw0 hw1 width stage).Cauchy) :
    (0 : Q') ≤ normCeiling hw0 hw1 width stage X :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (diagonalCeiling_nonnegative width _)
      (diagonalCeiling_nonnegative width _))

private theorem pairing_difference_add_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (xs anchor ys : DistanceSpan) :
    Equiv (pairing hw0 hw1 width (difference xs anchor ++ anchor) ys stage)
      (pairing hw0 hw1 width xs ys stage) :=
  Equiv.trans (pairing_add_left hw0 hw1 width (difference xs anchor) anchor ys stage)
    (Equiv.trans (Equiv_add (pairing_difference_left hw0 hw1 width xs anchor ys stage)
      (Equiv.refl _))
      (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.sub_add_cancel_eqv
        ((pairing hw0 hw1 width xs ys stage).approx n)
        ((pairing hw0 hw1 width anchor ys stage).approx n))))

/-- The difference-plus-anchor list need not equal x. Its diagonal is pinned
to x by the actual bilinear cancellation and reflected symmetry. -/
theorem diagonal_anchor_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x anchor : PhysicalSpan width) :
    leEv (pairing hw0 hw1 width x.val x.val stage)
      (add
        (add (distSq hw0 hw1 width stage x anchor) (distSq hw0 hw1 width stage x anchor))
        (add (pairing hw0 hw1 width anchor.val anchor.val stage)
          (pairing hw0 hw1 width anchor.val anchor.val stage))) := by
  let d := difference x.val anchor.val
  let total := d ++ anchor.val
  have hd : Physical width d := physical_difference x.property anchor.property
  have ht : Physical width total := physical_append hd anchor.property
  have hpin : Equiv (pairing hw0 hw1 width total total stage)
      (pairing hw0 hw1 width x.val x.val stage) :=
    Equiv.trans (pairing_difference_add_left hw0 hw1 width stage x.val anchor.val total)
      (Equiv.trans (pairing_symm hw0 hw1 width x.val total x.property ht stage)
        (pairing_difference_add_left hw0 hw1 width stage x.val anchor.val x.val))
  exact leEv_trans (leEv_of_equiv (Equiv.symm hpin))
    (pairing_add_bound hw0 hw1 width d anchor.val hd anchor.property stage)

private theorem four_bound {A B : CReal} {a b : Q'}
    (hA : leEv A (ofQ' a)) (hB : leEv B (ofQ' b)) :
    leEv (add (add A A) (add B B)) (ofQ' ((a+a)+(b+b))) := by
  have h := leEv_add (leEv_add hA hA) (leEv_add hB hB)
  rw [ofQ'_add, ofQ'_add, ofQ'_add] at h
  exact h

/-- Every term after the computed anchor has the same explicit diagonal cap. -/
theorem diagonal_le_normCeiling {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (X : (seminorm hw0 hw1 width stage).Cauchy)
    (n : Nat) (hn : normBase hw0 hw1 width stage X ≤ n) :
    leEv (pairing hw0 hw1 width (X.seq n).val (X.seq n).val stage)
      (ofQ' (normCeiling hw0 hw1 width stage X)) := by
  let anchor := X.seq (normBase hw0 hw1 width stage X)
  have hdist : leEv (distSq hw0 hw1 width stage (X.seq n) anchor) (ofQ' 1) :=
    X.isCauchy 1 (by decide) n (normBase hw0 hw1 width stage X) hn (Nat.le_refl _)
  exact leEv_trans (diagonal_anchor_bound hw0 hw1 width stage (X.seq n) anchor)
    (four_bound hdist (diagonal_le_ceiling hw0 hw1 width stage anchor))

end YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.diagonalCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.diagonalCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.diagonal_le_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.normBase
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.normCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds.diagonal_le_normCeiling
