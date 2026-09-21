/-
# Explicit finite-tail modulus for the quartic SU(2) heat majorant

The existing quartic prefix bound becomes geometric after its explicit label
cutoff.  Here that geometric comparison is combined with the constructive
base-power cutoff to give one computable index after which every finite tail
is below a supplied positive tolerance.

This is only a scalar majorant modulus.  It makes no statement about an
interacting action, Jacobi-weight removal, or a continuum limit.
-/

import YMGap.Continuum.SU2HeatQuarticPrefixBound

namespace YMGap.Continuum.SU2HeatQuarticTailCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2HeatQuarticPrefixBound

local infix:50 " ≈ " => Q'.eqv

/-- The fixed geometric scale after the quartic label cutoff. -/
def tailScale (w : Q') : Q' :=
  tailTerm w 4 (labelCutoff w) *
    HKConv.divPos 1 (1 + (-HalfPow.half))

/-- A positive rescaled tolerance.  The added one avoids any need to divide
by a possibly zero scale outside the strict-nome hypotheses. -/
def tailRescale (w epsilon : Q') : Q' :=
  HKConv.divPos epsilon (tailScale w + 1)

/-- The explicit absolute label after which every finite quartic tail is
below `epsilon`. -/
def tailCutoff (w epsilon : Q') : Nat :=
  labelCutoff w + powBaseCutoff HalfPow.half (tailRescale w epsilon)

theorem tailScale_nonnegative {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ tailScale w :=
  Q'.mul_nonneg _ _
    (tailTerm_nonneg (Q'.le_of_lt hw0) 4 (labelCutoff w))
    (HKConv.divPos_nonneg Q'.zero_le_one)

theorem tailRescale_pos (w : Q') {epsilon : Q'} (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < tailRescale w epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos hepsilon)

theorem tailRescale_budget {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hepsilon : (0 : Q') < epsilon) :
    tailScale w * tailRescale w epsilon ≤ epsilon := by
  have hs0 : (0 : Q') ≤ tailScale w := tailScale_nonnegative hw0
  have hd0 : (0 : Q') ≤ tailRescale w epsilon :=
    Q'.le_of_lt (tailRescale_pos w hepsilon)
  have hden : (0 : Q') < tailScale w + 1 :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hs0)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  have hle : tailScale w * tailRescale w epsilon ≤
      (tailScale w + 1) * tailRescale w epsilon :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.add_le_self_of_nonneg (tailScale w) 1 Q'.zero_le_one) hd0
  have heq : (tailScale w + 1) * tailRescale w epsilon ≈ epsilon :=
    Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (tailScale w + 1) (tailRescale w epsilon))
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hden))
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv heq)

/-- The closed geometric quartic tail is below `epsilon` at every relative
index past the explicit power cutoff. -/
theorem closedTail_small {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hepsilon : (0 : Q') < epsilon)
    (M : Nat) (hM : powBaseCutoff HalfPow.half (tailRescale w epsilon) ≤ M) :
    geoTailBase (tailTerm w 4 (labelCutoff w)) HalfPow.half M ≤ epsilon := by
  have hp : HalfPow.half ^ M ≤ tailRescale w epsilon :=
    Q'.le_trans' _ _ _
      (pow_base_antitone HalfPow.half_nonneg (Q'.le_of_lt (by decide : HalfPow.half < (1 : Q'))) hM)
      (pow_base_le_cutoff (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) (tailRescale_pos w hepsilon))
  have hs0 : (0 : Q') ≤ tailScale w := tailScale_nonnegative hw0
  have heq : geoTailBase (tailTerm w 4 (labelCutoff w)) HalfPow.half M ≈
      tailScale w * HalfPow.half ^ M := by
    unfold geoTailBase tailScale
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (tailTerm w 4 (labelCutoff w)) (HalfPow.half ^ M)
        (HKConv.divPos 1 (1 + (-HalfPow.half))))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (tailTerm w 4 (labelCutoff w)) _ _
          (Q'.mul_comm_eqv (HalfPow.half ^ M)
            (HKConv.divPos 1 (1 + (-HalfPow.half)))))
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (tailTerm w 4 (labelCutoff w))
            (HKConv.divPos 1 (1 + (-HalfPow.half))) (HalfPow.half ^ M))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hp hs0)
      (tailRescale_budget hw0 hepsilon))

/-- Every finite block beginning after `tailCutoff w epsilon` has quartic heat
majorant at most `epsilon`.  The bound is uniform in the finite block length. -/
theorem finite_shifted_tail_le {w epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hepsilon : (0 : Q') < epsilon) (N L : Nat)
    (hN : tailCutoff w epsilon ≤ N) :
    finSum (fun k => tailTerm w 4 (N + k)) L ≤ epsilon := by
  have hlabel : labelCutoff w ≤ N := by
    unfold tailCutoff at hN
    omega
  let M := N - labelCutoff w
  have hM : powBaseCutoff HalfPow.half (tailRescale w epsilon) ≤ M := by
    unfold tailCutoff at hN
    dsimp [M]
    omega
  have hrewrite : labelCutoff w + M = N := by
    dsimp [M]
    exact Nat.add_sub_of_le hlabel
  have hterm : ∀ k : Nat,
      tailTerm w 4 (N + k) ≤
        geoIncrBase (tailTerm w 4 (labelCutoff w)) HalfPow.half (M + k) := by
    intro k
    rw [← hrewrite, Nat.add_assoc]
    exact shifted_geometric hw0 hw1 (M + k)
  exact Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _ hterm L)
    (Q'.le_trans' _ _ _
      (geoTailBase_series_le
        (tailTerm_nonneg (Q'.le_of_lt hw0) 4 (labelCutoff w))
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) M L)
      (closedTail_small hw0 hepsilon M hM))

end YMGap.Continuum.SU2HeatQuarticTailCutoff

#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.tailScale
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.tailRescale
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.tailCutoff
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.tailScale_nonnegative
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.tailRescale_pos
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.tailRescale_budget
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.closedTail_small
#print axioms YMGap.Continuum.SU2HeatQuarticTailCutoff.finite_shifted_tail_le
