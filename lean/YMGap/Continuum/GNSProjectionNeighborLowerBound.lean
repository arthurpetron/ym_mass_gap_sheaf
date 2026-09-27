/-
# Ordered-neighbor lower bound for completed projection residuals

Each directed neighboring cross term is charged to both endpoint residual
energies. Separate row and column incidence bounds keep the total cost at
twice the maximum off-diagonal degree, with no sign discarded.
-/

import YMGap.Continuum.GNSProjectionSignedEnergy
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.RCSignedPairBudget (neg_mono)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (A.approx n) (B.approx n)))

private theorem rc_neg_zero : RCneg RCzero = RCzero := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => (by decide : Q'.eqv (-(0 : Q')) 0)))

private theorem rc_neg_add (a b : RC) :
    RCneg (RCadd a b) = RCadd (RCneg a) (RCneg b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.neg (.add (.var 0) (.var 1)))
      (.add (.neg (.var 0)) (.neg (.var 1)))
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem rc_scale_zero (a : RC) : RCscale (Q'.ofNat 0) a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem rc_scale_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n + 1)) a = RCadd a (RCscale (Q'.ofNat n) a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))
          (Q'.add_comm_eqv _ _)))))

private theorem sumOn_zero {A : Type} (xs : List A) :
    sumOn xs (fun _ => RCzero) = RCzero := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp only [sumOn, ih, rc_zero_add]

private theorem sumOn_neg {A : Type} (xs : List A) (f : A → RC) :
    sumOn xs (fun i => RCneg (f i)) = RCneg (sumOn xs f) := by
  induction xs with
  | nil => exact rc_neg_zero.symm
  | cons i rest ih =>
      simp only [sumOn, ih, rc_neg_add]

private theorem sumOn_select {A : Type} (xs : List A) (select : A → Bool)
    (a : RC) :
    sumOn xs (fun i => if select i then a else RCzero) =
      RCscale (Q'.ofNat (xs.filter select).length) a := by
  induction xs with
  | nil => exact (rc_scale_zero a).symm
  | cons i rest ih =>
      cases hs : select i with
      | false =>
          simp only [sumOn, hs, Bool.false_eq_true, if_false, List.filter_cons,
            ih, rc_zero_add]
      | true =>
          simp only [sumOn, hs, if_true, List.filter_cons, List.length_cons, ih]
          exact (rc_scale_succ (rest.filter select).length a).symm

private theorem selected_le {A : Type} (xs : List A) (select : A → Bool)
    (a : RC) (ha : RCnonneg a) (degree : Nat)
    (hc : (xs.filter select).length ≤ degree) :
    RCle (sumOn xs (fun i => if select i then a else RCzero))
      (RCscale (Q'.ofNat degree) a) := by
  rw [sumOn_select]
  exact RCscale_scalar_mono (ofNat_le_ofNat hc) ha

private theorem sumOn_swap {A B : Type} (xs : List A) (ys : List B)
    (f : A → B → RC) :
    sumOn xs (fun i => sumOn ys (fun j => f i j)) =
      sumOn ys (fun j => sumOn xs (fun i => f i j)) := by
  induction xs with
  | nil => simp only [sumOn, sumOn_zero]
  | cons i rest ih =>
      simp only [sumOn, ih]
      exact (sumOn_add ys (fun j => f i j)
        (fun j => sumOn rest (fun k => f k j))).symm

private theorem double_scale (degree : Nat) (e : Q') (a : RC) :
    RCadd (RCscale (Q'.ofNat degree) (RCscale e a))
      (RCscale (Q'.ofNat degree) (RCscale e a)) =
      RCscale ((2 : Q') * Q'.ofNat degree * e) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
      (by decide)
      (fun | 0 => Q'.ofNat degree | 1 => e | _ => A.approx n)))

variable {D : GNSData} {Index : Type} [DecidableEq Index]
  (P : Family D Index) (near : Index → Index → Bool)

private def offEdge (i j : Index) : Bool :=
  if i = j then false else near i j

/-- A directed off-diagonal neighbor estimate loses at most twice the
maximum off-diagonal incidence times its endpoint coefficient. Both row and
column counts are explicit, so no symmetry of `near` is silently assumed. -/
theorem neighboringCross_lower (tests : List Index) (x : GNSCompletionSpace D)
    (degree : Nat) (e : Q') (he : (0 : Q') ≤ e)
    (hrow : ∀ i, i ∈ tests →
      (tests.filter (fun j => offEdge near i j)).length ≤ degree)
    (hcolumn : ∀ j, j ∈ tests →
      (tests.filter (fun i => offEdge near i j)).length ≤ degree)
    (hpair : ∀ i j, i ∈ tests → j ∈ tests → i ≠ j → near i j = true →
      RCle (RCneg (RCscale e
        (RCadd (normSq (P.residual i x)) (normSq (P.residual j x)))))
        (D.cinnerCompl (P.residual i x) (P.residual j x))) :
    RCle (RCneg (RCscale ((2 : Q') * Q'.ofNat degree * e)
      (P.finalEnergy tests x))) (P.neighboringCross near tests x) := by
  let E : Index → RC := fun i => normSq (P.residual i x)
  let edge : Index → Index → Bool := offEdge near
  let charge : Index → Index → RC := fun i j =>
    if edge i j then RCscale e (RCadd (E i) (E j)) else RCzero
  let first : Index → Index → RC := fun i j =>
    if edge i j then RCscale e (E i) else RCzero
  let second : Index → Index → RC := fun i j =>
    if edge i j then RCscale e (E j) else RCzero
  have heE (i : Index) : RCnonneg (RCscale e (E i)) := by
    change RCle RCzero (RCscale e (E i))
    rw [← RCscale_RCzero e]
    exact RCscale_mono he (D.cinner_self_nonneg _)
  have hfirst (i : Index) (hi : i ∈ tests) :
      RCle (sumOn tests (first i))
        (RCscale (Q'.ofNat degree) (RCscale e (E i))) :=
    selected_le tests (edge i) _ (heE i) degree (hrow i hi)
  have hsecond (j : Index) (hj : j ∈ tests) :
      RCle (sumOn tests (fun i => second i j))
        (RCscale (Q'.ofNat degree) (RCscale e (E j))) :=
    selected_le tests (fun i => edge i j) _ (heE j) degree (hcolumn j hj)
  have hfirstSum : RCle
      (sumOn tests (fun i => sumOn tests (first i)))
      (RCscale (Q'.ofNat degree) (RCscale e (P.finalEnergy tests x))) := by
    have h := sumOn_mono tests _ _ hfirst
    rw [sumOn_scale, sumOn_scale] at h
    exact h
  have hsecondSum : RCle
      (sumOn tests (fun i => sumOn tests (second i)))
      (RCscale (Q'.ofNat degree) (RCscale e (P.finalEnergy tests x))) := by
    rw [sumOn_swap tests tests second]
    have h := sumOn_mono tests _ _ hsecond
    rw [sumOn_scale, sumOn_scale] at h
    exact h
  have hcharge_split (i j : Index) :
      charge i j = RCadd (first i j) (second i j) := by
    cases h : edge i j with
    | false => simp only [charge, first, second, h, Bool.false_eq_true,
        if_false, rc_zero_add]
    | true => simp only [charge, first, second, h, if_true, RCscale_RCadd]
  have htotal :
      sumOn tests (fun i => sumOn tests (charge i)) =
      RCadd
        (sumOn tests (fun i => sumOn tests (first i)))
        (sumOn tests (fun i => sumOn tests (second i))) := by
    have hr (i : Index) : sumOn tests (charge i) =
        RCadd (sumOn tests (first i)) (sumOn tests (second i)) := by
      calc
        sumOn tests (charge i) =
            sumOn tests (fun j => RCadd (first i j) (second i j)) := by
          apply congrArg (sumOn tests)
          funext j
          exact hcharge_split i j
        _ = _ := sumOn_add tests _ _
    calc
      sumOn tests (fun i => sumOn tests (charge i)) =
          sumOn tests (fun i => RCadd (sumOn tests (first i))
            (sumOn tests (second i))) := by
        apply congrArg (sumOn tests)
        funext i
        exact hr i
      _ = _ := sumOn_add tests _ _
  have hcharge : RCle (sumOn tests (fun i => sumOn tests (charge i)))
      (RCscale ((2 : Q') * Q'.ofNat degree * e) (P.finalEnergy tests x)) := by
    rw [htotal]
    exact RCle_trans (RCadd_le_add hfirstSum hsecondSum)
      (by rw [double_scale]; exact RCle_refl _)
  have hpoint (i j : Index) (hi : i ∈ tests) (hj : j ∈ tests) :
      RCle (RCneg (charge i j))
        (if i = j then RCzero else if near i j then
          D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero) := by
    by_cases hij : i = j
    · simp only [charge, edge, offEdge, hij, if_true, rc_neg_zero]
      exact RCle_refl _
    · cases hn : near i j with
      | false =>
          simp only [charge, edge, offEdge, hij, if_false, hn,
            Bool.false_eq_true, rc_neg_zero]
          exact RCle_refl _
      | true =>
          simpa only [charge, edge, offEdge, hij, if_false, hn, if_true, E]
            using hpair i j hi hj hij hn
  have hlow : RCle
      (sumOn tests (fun i => sumOn tests (fun j => RCneg (charge i j))))
      (P.neighboringCross near tests x) := by
    unfold neighboringCross
    apply sumOn_mono
    intro i hi
    apply sumOn_mono
    intro j hj
    exact hpoint i j hi hj
  simp only [sumOn_neg] at hlow
  exact RCle_trans (neg_mono hcharge) hlow

#print axioms neighboringCross_lower

end YMGap.Continuum.GNSProjectionSweep.Family
