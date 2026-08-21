/-
# Constructive elimination of the head mean-zero coordinate

For a finite weighted carrier with strictly positive head weight, every
weighted-centered vector is constructively and uniquely represented by its
tail coordinates: the head coefficient is the negative tail weighted sum
divided by the head weight.  This module proves the lift is centered and
constructively recovers tail coordinates from every centered full vector.

Given exact identifications of two reduced matrix quadratics with the lifted
canonical penalized forms, these coordinates construct the full
`FiniteCenteredTwoSidedRestriction` consumed by the reduced LDL compiler.
The reduced matrices and their identifications are still inputs here; their
canonical pullback construction is the next finite-algebra frontier.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate

namespace YMGap.Continuum.FiniteRationalHeadCenteredCoordinates

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem range_succ_shift (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        List.range (Nat.succ n + 1) =
            List.range (n + 1) ++ [n + 1] := by
          simpa only [Nat.succ_eq_add_one] using
            (List.range_succ (n := n + 1))
        _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] :=
          congrArg (fun items => items ++ [n + 1]) ih
        _ = 0 :: (List.range (n + 1)).map Nat.succ := by
          simp only [List.range_succ, List.map_append, List.map,
            List.cons_append, Nat.succ_eq_add_one]

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem eqv_of_le_of_le_local
    {a b : Q'} (hab : a ≤ b) (hba : b ≤ a) : a ≈ b :=
  Int.le_antisymm hab hba

private theorem eqv_divPos_of_mul_local
    {a numerator denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hmul : a * denominator ≈ numerator) :
    a ≈ Q'.divPos numerator denominator hdenominator := by
  apply eqv_of_le_of_le_local
  · exact Q'.le_divPos_of_mul_le numerator denominator hdenominator
      (Q'.le_of_eqv hmul)
  · exact Q'.divPos_le_of_le_mul numerator denominator hdenominator
      (Q'.ge_of_eqv hmul)

private theorem left_eqv_neg_of_add_eqv_zero
    {a b : Q'} (hadd : a + b ≈ 0) : a ≈ -b := by
  have hstart : a ≈ (-b) + (a + -(-b)) :=
    Q'.add_sub_cancel_eqv a (-b)
  have hinner : a + -(-b) ≈ a + b :=
    Q'.add_eqv_congr_left a _ _ (Q'.neg_neg_eqv b)
  have hmiddle : (-b) + (a + -(-b)) ≈ (-b) + (a + b) :=
    Q'.add_eqv_congr_left (-b) _ _ hinner
  have hend : (-b) + (a + b) ≈ -b := by
    refine Q'.eqv_trans _ ((-b) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (-b) _ _ hadd
    · exact Q'.eqv_of_eq (Q'.add_zero' (-b))
  exact Q'.eqv_trans _ _ _ hstart
    (Q'.eqv_trans _ _ _ hmiddle hend)

/-! ## 1. Explicit head elimination -/

/-- The weighted tail sum in reduced coordinates `0, ..., n-1`, corresponding
to full coordinates `1, ..., n`. -/
def finiteTailWeightedMean
    (n : Nat) (weight reduced : Nat → Q') : Q' :=
  listQSum
    (fun k => reduced k * weight (k + 1))
    (List.range n)

/-- Lift tail coordinates to a full `(n+1)`-coordinate centered vector. -/
def finiteHeadCenteredLift
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (reduced : Nat → Q') : Nat → Q'
  | 0 => Q'.divPos
      (-(finiteTailWeightedMean n weight reduced))
      (weight 0) hhead
  | k + 1 => reduced k

/-- Split the full weighted mean into its head term and shifted tail sum. -/
theorem finiteWeightedMean_succ_decompose
    (n : Nat) (weight coefficient : Nat → Q') :
    finiteWeightedMean (n + 1) weight coefficient ≈
      coefficient 0 * weight 0 +
        finiteTailWeightedMean n weight (fun k => coefficient (k + 1)) := by
  unfold finiteWeightedMean finiteTailWeightedMean
  rw [range_succ_shift]
  simp only [listQSum]
  rw [listQSum_map_local]
  exact Q'.eqv_refl _

/-- The explicit head lift is exactly weighted-centered. -/
theorem finiteHeadCenteredLift_centered
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (reduced : Nat → Q') :
    finiteWeightedMean (n + 1) weight
        (finiteHeadCenteredLift n weight hhead reduced) ≈ 0 := by
  let tail := finiteTailWeightedMean n weight reduced
  have hsplit := finiteWeightedMean_succ_decompose
    n weight (finiteHeadCenteredLift n weight hhead reduced)
  have hheadmul :
      finiteHeadCenteredLift n weight hhead reduced 0 * weight 0 ≈
        -tail := by
    exact Q'.divPos_mul_eqv (-tail) (weight 0) hhead
  refine Q'.eqv_trans _
    (finiteHeadCenteredLift n weight hhead reduced 0 * weight 0 + tail)
    _ hsplit ?_
  exact Q'.eqv_trans _ ((-tail) + tail) _
    (Q'.add_eqv_congr_right _ _ tail hheadmul)
    (Q'.neg_add_self_eqv tail)

/-- Every centered full vector is constructively recovered from its literal
tail coordinates. -/
def finiteHeadCenteredLift_complete
    (n : Nat) (weight : Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (coefficient : Nat → Q')
    (hcenter : finiteWeightedMean (n + 1) weight coefficient ≈ 0) :
    { reduced : Nat → Q' //
      ∀ i, i < n + 1 →
        coefficient i ≈
          finiteHeadCenteredLift n weight hhead reduced i } := by
  let reduced : Nat → Q' := fun k => coefficient (k + 1)
  refine ⟨reduced, ?_⟩
  intro i hi
  cases i with
  | zero =>
      have hsplit := finiteWeightedMean_succ_decompose
        n weight coefficient
      have hadd :
          coefficient 0 * weight 0 +
              finiteTailWeightedMean n weight reduced ≈ 0 :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm hsplit) hcenter
      have hmul :
          coefficient 0 * weight 0 ≈
            -(finiteTailWeightedMean n weight reduced) :=
        left_eqv_neg_of_add_eqv_zero hadd
      exact eqv_divPos_of_mul_local hhead hmul
  | succ k =>
      exact Q'.eqv_refl _

/-! ## 2. Constructor for the reduced two-sided restriction -/

/-- Once reduced upper/lower matrix identities are supplied, the positive
head weight generates all remaining centered-coordinate restriction data. -/
def finiteHeadCenteredTwoSidedRestriction
    (n : Nat) (q : Q') (weight : Nat → Q')
    (kernel : Nat → Nat → Q')
    (hhead : (0 : Q') < weight 0)
    (upperMatrix lowerMatrix : Nat → Nat → Q')
    (upperIdentify :
      ∀ reduced,
        finiteMatrixQuadratic n upperMatrix reduced ≈
          finitePenalizedReversibleQuadratic
            (n + 1) q weight kernel
            (finiteHeadCenteredLift n weight hhead reduced))
    (lowerIdentify :
      ∀ reduced,
        finiteMatrixQuadratic n lowerMatrix reduced ≈
          finiteLowerPenalizedReversibleQuadratic
            (n + 1) q weight kernel
            (finiteHeadCenteredLift n weight hhead reduced)) :
    FiniteCenteredTwoSidedRestriction (n + 1) q weight kernel where
  reducedSize := n
  lift := finiteHeadCenteredLift n weight hhead
  liftCentered := finiteHeadCenteredLift_centered n weight hhead
  complete := finiteHeadCenteredLift_complete n weight hhead
  upperMatrix := upperMatrix
  lowerMatrix := lowerMatrix
  upperIdentify := upperIdentify
  lowerIdentify := lowerIdentify

end YMGap.Continuum.FiniteRationalHeadCenteredCoordinates

#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredCoordinates.finiteWeightedMean_succ_decompose
#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredCoordinates.finiteHeadCenteredLift_centered
#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredCoordinates.finiteHeadCenteredLift_complete
#print axioms
  YMGap.Continuum.FiniteRationalHeadCenteredCoordinates.finiteHeadCenteredTwoSidedRestriction
