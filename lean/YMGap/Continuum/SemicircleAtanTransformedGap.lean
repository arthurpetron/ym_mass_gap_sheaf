/-
# Abel gap engine for the transformed atan Darboux sums

This module isolates the finite ordered-sum estimate needed after
`SemicircleAtanTransformedSqueeze`.  If the cell widths `w_j` are bounded by a
common nonnegative mesh `h` and the sampled kernel values `f_j` decrease, then

  sum w_j f_j <= sum w_j f_(j+1) + h f_0.

The proof is an exact finite Abel telescope over `Q'`.  It contains no
analytic limit and makes no assertion yet about the concrete Mobius nodes.
-/

import YMGap.Continuum.SemicircleAtanTransformedSqueeze
import YMGap.Constructive.FinSumAlg
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SemicircleAtanTransformedGap

open YMGap.Constructive

private def dropPairL : RingNormaliser.PolyExpr :=
  .add (.add (.var 0) (.neg (.var 1)))
    (.add (.var 1) (.neg (.var 2)))

private def dropPairR : RingNormaliser.PolyExpr :=
  .add (.var 0) (.neg (.var 2))

private theorem dropPair_normal :
    RingNormaliser.normalize dropPairL =
      RingNormaliser.normalize dropPairR := by decide

private theorem drop_pair (a b c : Q') :
    ((a + -b) + (b + -c)).eqv (a + -c) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    dropPairL dropPairR dropPair_normal
    (fun
      | 0 => a
      | 1 => b
      | _ => c)
  simpa [dropPairL, dropPairR, RingNormaliser.eval] using h

/-- Exact finite telescope of adjacent drops. -/
theorem finSum_adjacent_drop (f : Nat → Q') : ∀ n,
    (RationalTail.finSum (fun j => f j + -f (j+1)) n).eqv
      (f 0 + -f n)
  | 0 => by
      show (0 : Q').eqv (f 0 + -f 0)
      exact Q'.eqv_symm (Q'.add_neg_self_eqv (f 0))
  | n + 1 => by
      show (RationalTail.finSum (fun j => f j + -f (j+1)) n +
          (f n + -f (n+1))).eqv (f 0 + -f (n+1))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f n + -f (n+1))
          (finSum_adjacent_drop f n)) ?_
      exact drop_pair (f 0) (f n) (f (n+1))

private theorem weighted_split (w a b : Q') :
    (w*b + w*(a + -b)).eqv (w*a) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_add_eqv w b (a + -b))) ?_
  refine Q'.mul_eqv_congr_left w _ a ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left b (a + -b) ((-b) + a)
      (Q'.add_comm_eqv a (-b))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv b (-b) a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (b + -b) 0 a (Q'.add_neg_self_eqv b)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' a)

private theorem neg_nonpos_of_nonneg {x : Q'} (hx : (0 : Q') ≤ x) :
    -x ≤ (0 : Q') := by
  have h : (0 : Q') + (-x) ≤ x + (-x) :=
    Q'.add_le_add_right 0 x (-x) hx
  refine Q'.le_trans' _ _ _ ?_
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_neg_self_eqv x)))
  exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-x)))

private theorem finSum_le_finSum_of_termwise_lt
    (a b : Nat → Q') : ∀ n,
    (∀ j, j < n → a j ≤ b j) →
      RationalTail.finSum a n ≤ RationalTail.finSum b n
  | 0, _ => Q'.le_refl' 0
  | n + 1, h => by
      show RationalTail.finSum a n + a n ≤
        RationalTail.finSum b n + b n
      exact Q'.add_le_add
        (finSum_le_finSum_of_termwise_lt a b n
          (fun j hj => h j (Nat.lt_succ_of_lt hj)))
        (h n (Nat.lt_succ_self n))

/-- Finite Abel estimate for a decreasing sampled function on a partition with
uniformly bounded cell widths. -/
theorem weighted_antitone_gap
    (w f : Nat → Q') (h : Q') (n : Nat)
    (hh : (0 : Q') ≤ h)
    (hw : ∀ j, j < n → w j ≤ h)
    (hf : ∀ j, j < n → f (j+1) ≤ f j)
    (hfn : (0 : Q') ≤ f n) :
    RationalTail.finSum (fun j => w j * f j) n ≤
      RationalTail.finSum (fun j => w j * f (j+1)) n + h * f 0 := by
  let drop : Nat → Q' := fun j => f j + -f (j+1)
  have hterm : ∀ j, j < n →
      w j * f j ≤ w j * f (j+1) + h * drop j := by
    intro j hj
    have hdrop : (0 : Q') ≤ drop j := Q'.sub_nonneg_of_le (hf j hj)
    have hmul : w j * drop j ≤ h * drop j :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (hw j hj) hdrop
    have hadd : w j * f (j+1) + w j * drop j ≤
        w j * f (j+1) + h * drop j :=
      Q'.add_le_add_left _ _ _ hmul
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (weighted_split (w j) (f j) (f (j+1)))) hadd
  have hsum : RationalTail.finSum (fun j => w j * f j) n ≤
      RationalTail.finSum (fun j => w j * f (j+1) + h * drop j) n := by
    exact finSum_le_finSum_of_termwise_lt _ _ n hterm
  have hsplit :
      (RationalTail.finSum (fun j => w j * f (j+1) + h * drop j) n).eqv
        (RationalTail.finSum (fun j => w j * f (j+1)) n +
          h * RationalTail.finSum drop n) := by
    refine Q'.eqv_trans _ _ _
      (RationalTail.finSum_add (fun j => w j * f (j+1))
        (fun j => h * drop j) n) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (RationalTail.const_mul_finSum drop h n))
  have htel : (h * RationalTail.finSum drop n).eqv
      (h * (f 0 + -f n)) :=
    Q'.mul_eqv_congr_left h _ _ (finSum_adjacent_drop f n)
  have hdrop_le : f 0 + -f n ≤ f 0 := by
    have hn := neg_nonpos_of_nonneg hfn
    have ha := Q'.add_le_add_left (f 0) (-f n) 0 hn
    exact Q'.le_trans' _ _ _ ha
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (f 0))))
  have hlast : h * RationalTail.finSum drop n ≤ h * f 0 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htel)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hdrop_le hh)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.add_le_add_left _ _ _ hlast))

end YMGap.Continuum.SemicircleAtanTransformedGap

#print axioms YMGap.Continuum.SemicircleAtanTransformedGap.finSum_adjacent_drop
#print axioms YMGap.Continuum.SemicircleAtanTransformedGap.weighted_antitone_gap
