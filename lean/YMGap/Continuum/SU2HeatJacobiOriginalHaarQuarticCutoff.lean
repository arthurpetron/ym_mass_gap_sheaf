/-
# Computed all-later cutoffs for the ORIGINAL Haar quartic insertion

The margin is epsilon/2. The original q tail is targeted at epsilon/64,
and the original q*q tail at epsilon/(4*(1+c(q))). One explicit maximum
includes those two computed tail cutoffs and the original positive-source
head cutoff. Every later SAME inclusive K therefore pays total error plus
margin at most epsilon.

The final insertion is bounded by (c(q)+epsilon) times the SAME original
odd partition. Its nonnegativity is proved by the existing actual source
producer, not supplied. No inverse heat floor, signed-source estimate,
OWN-variance bound, changing-family survival or continuum claim is made.
-/

import YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticBound

namespace YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2HeatJacobiFinitePrefixMargin
open YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticBound
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (spacingLabelCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison (selectedInsertion)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks oddMass

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

def prefixMargin (epsilon : Q') : Q' := HalfPow.half*epsilon

def qTailTolerance (epsilon : Q') : Q' := Q'.mkPos 1 64 (by decide)*epsilon

private theorem coefficient_nonnegative (q : Q') : (0 : Q')≤quarticProfileCoefficient q :=
  Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg (1-q)))

private theorem toleranceDenominator_positive (q : Q') :
    (0 : Q')<4*(1+quarticProfileCoefficient q) :=
  Q'.mul_pos (by decide) (Q'.pos_of_lt_of_le (by decide : (0 : Q')<1)
    (Q'.add_le_self_of_nonneg 1 _ (coefficient_nonnegative q)))

/-- This is an actual positive division by 4*(1+c), not an inverse heat floor. -/
def squaredTailTolerance (q epsilon : Q') : Q' :=
  Q'.divPos epsilon (4*(1+quarticProfileCoefficient q)) (toleranceDenominator_positive q)

/-- Both actual tail targets and the original head guard are computed here. -/
def quarticCutoff (q epsilon : Q') : Nat :=
  max (headCutoff q)
    (max (inclusiveTailCutoff q (qTailTolerance epsilon))
      (inclusiveTailCutoff (q*q) (squaredTailTolerance q epsilon)))

private theorem cutoff_q_tail (q epsilon : Q') (K : Nat) (hK : quarticCutoff q epsilon≤K) :
    inclusiveTailCutoff q (qTailTolerance epsilon)≤K :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hK

private theorem cutoff_squared_tail (q epsilon : Q') (K : Nat)
    (hK : quarticCutoff q epsilon≤K) :
    inclusiveTailCutoff (q*q) (squaredTailTolerance q epsilon)≤K :=
  Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK

/-- Every later K satisfies the original head and BOTH inclusive K+1 guards. -/
theorem cutoff_guards (q epsilon : Q') (K : Nat) (hK : quarticCutoff q epsilon≤K) :
    headCutoff q≤K ∧ spacingLabelCutoff q≤K+1 ∧ spacingLabelCutoff (q*q)≤K+1 := by
  have hq := cutoff_q_tail q epsilon K hK
  have hqq := cutoff_squared_tail q epsilon K hK
  unfold inclusiveTailCutoff at hq hqq
  exact ⟨Nat.le_trans (Nat.le_max_left _ _) hK, by omega, by omega⟩

private theorem squaredTolerance_pin (q epsilon : Q') :
    (1+quarticProfileCoefficient q)*squaredTailTolerance q epsilon ≈ quarter*epsilon := by
  let c := quarticProfileCoefficient q
  let d := squaredTailTolerance q epsilon
  have hdiv : d*(4*(1+c)) ≈ epsilon :=
    Q'.divPos_mul_eqv _ _ (toleranceDenominator_positive q)
  have hcancel : quarter*(d*(4*(1+c))) ≈ (1+c)*d :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.mul (.const 4) (.add (.const 1) (.var 2)))))
        (.mul (.mul (.var 0) (.const 4)) (.mul (.add (.const 1) (.var 2)) (.var 1)))
        (by decide) (fun | 0 => quarter | 1 => d | _ => c))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((1+c)*d) (by decide : quarter*4 ≈ 1))
        (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hcancel)
    (Q'.mul_eqv_congr_left quarter _ _ hdiv)

/-- Full original prefix error plus its constructed margin is at most epsilon
at EVERY later common cutoff; no tail estimates are assumed. -/
theorem quarticPrefixError_budget {q epsilon : Q'}
    (hq0 : (0 : Q')<q) (hq1 : q<(1 : Q')) (he : (0 : Q')<epsilon)
    (K : Nat) (hK : quarticCutoff q epsilon≤K) :
    quarticPrefixError q K+prefixMargin epsilon≤epsilon := by
  have htq : (0 : Q')<qTailTolerance epsilon := Q'.mul_pos (by decide) he
  have htqq : (0 : Q')<squaredTailTolerance q epsilon := Q'.divPos_pos _ _ _ he
  have hq := inclusivePrefixTail_small hq0 hq1 htq K (cutoff_q_tail q epsilon K hK)
  have hqq := inclusivePrefixTail_small (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) htqq K
    (cutoff_squared_tail q epsilon K hK)
  have hfirst : 16*inclusivePrefixTail q K≤quarter*epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 16 hq (by decide))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv 16 (Q'.mkPos 1 64 (by decide)) epsilon))
        (Q'.mul_eqv_congr_right _ _ epsilon
          (by decide : (16 : Q')*Q'.mkPos 1 64 (by decide) ≈ quarter))))
  have hc := coefficient_nonnegative q
  have hc1 : quarticProfileCoefficient q≤1+quarticProfileCoefficient q :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hsecond : quarticProfileCoefficient q*inclusivePrefixTail (q*q) K≤quarter*epsilon :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hqq hc)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hc1 (Q'.le_of_lt htqq))
        (Q'.le_of_eqv (squaredTolerance_pin q epsilon)))
  have hhalves : quarter*epsilon+quarter*epsilon ≈ HalfPow.half*epsilon :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv quarter quarter epsilon))
      (Q'.mul_eqv_congr_right _ _ epsilon (by decide : quarter+quarter ≈ HalfPow.half))
  have herror : quarticPrefixError q K≤HalfPow.half*epsilon :=
    Q'.le_trans' _ _ _ (Q'.add_le_add hfirst hsecond) (Q'.le_of_eqv hhalves)
  have hsum : HalfPow.half*epsilon+prefixMargin epsilon ≈ epsilon :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv HalfPow.half HalfPow.half epsilon))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ epsilon (by decide : HalfPow.half+HalfPow.half ≈ 1))
        (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ herror) (Q'.le_of_eqv hsum)

/-- Actual selected insertion against the SAME original source, spectators,
depth and odd partition, with fully computed all-later cutoff data. -/
theorem selectedChordInsertion_le_tolerance {q epsilon : Q'}
    (hq0 : (0 : Q')<q) (hq1 : q<(1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide)≤q) (he : (0 : Q')<epsilon)
    (K width depth i : Nat) (hK : quarticCutoff q epsilon≤K)
    (hi : i∈activeBlocks width) :
    selectedInsertion q K width depth i
      (quarticChordInsertion q K (scalarAt (N width+i) i))≤
      (quarticProfileCoefficient q+epsilon)*oddMass q K width depth := by
  have hg := cutoff_guards q epsilon K hK
  have hmargin : (0 : Q')<prefixMargin epsilon := Q'.mul_pos (by decide) he
  have hbound := selectedChordInsertion_le_original hq0 hq1 hq hmargin
    K width depth i hg.1 hg.2.1 hg.2.2 hi
  have hmass : (0 : Q')≤oddMass q K width depth :=
    Q'.le_of_lt (oddMass_positive hq0 hq1 K width hg.1 depth)
  exact Q'.le_trans' _ _ _ hbound
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_add_left _ _ _ (quarticPrefixError_budget hq0 hq1 he K hK)) hmass)

#print axioms prefixMargin
#print axioms qTailTolerance
#print axioms squaredTailTolerance
#print axioms quarticCutoff
#print axioms cutoff_guards
#print axioms quarticPrefixError_budget
#print axioms selectedChordInsertion_le_tolerance

end YMGap.Continuum.SU2HeatJacobiOriginalHaarQuarticCutoff
