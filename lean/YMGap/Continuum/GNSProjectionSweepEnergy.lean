/-
# Bounded-incidence final residual energy versus actual sweep loss

Row bounds come from the constructed sparse correction lists. Summing them
charges each ACTUAL intermediate step loss at most once per neighboring test
index. Row and column incidence bounds g therefore give g^2 times the exact
Pythagorean sweep loss. No coercivity or strict contraction is assumed.
-/

import YMGap.Continuum.GNSProjectionSweepSparseRow

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem swap (a b c : RC) : RCadd a (RCadd b c) = RCadd b (RCadd a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
        (Q'.add_assoc_eqv _ _ _))))

private theorem exchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd c a) (RCadd b d) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn d ?_
  intro E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 2) (.var 0)) (.add (.var 1) (.var 3)))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => E.approx n)))

private theorem scale_zero (a : RC) : RCscale (Q'.ofNat 0) a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv _))

private theorem scale_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)))))

private theorem add_nonneg {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rw [zero_add] at h
  exact h

private theorem le_add_of_nonneg_left (a b : RC) (ha : RCnonneg a) :
    RCle b (RCadd a b) := by
  have h := RCadd_le_add ha (RCle_refl b)
  rw [zero_add] at h
  exact h

/-- Finite scalar sum with its original indexing list, including multiplicity. -/
def sumOn {A : Type} : List A → (A → RC) → RC
  | [], _ => RCzero
  | i :: rest, f => RCadd (f i) (sumOn rest f)

theorem sumOn_mono {A : Type} (xs : List A) (f g : A → RC)
    (h : ∀ i, i ∈ xs → RCle (f i) (g i)) : RCle (sumOn xs f) (sumOn xs g) := by
  induction xs with
  | nil => exact RCle_refl _
  | cons i rest ih =>
      exact RCadd_le_add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

theorem sumOn_scale {A : Type} (xs : List A) (f : A → RC) (c : Q') :
    sumOn xs (fun i => RCscale c (f i)) = RCscale c (sumOn xs f) := by
  induction xs with
  | nil => exact (RCscale_RCzero c).symm
  | cons i rest ih => simp only [sumOn, ih, RCscale_RCadd]

private theorem sumOn_step {A : Type} (xs : List A) (select : A → Bool)
    (a : RC) (f : A → RC) :
    sumOn xs (fun i => if select i then RCadd a (f i) else f i) =
      RCadd (RCscale (Q'.ofNat (xs.filter select).length) a) (sumOn xs f) := by
  induction xs with
  | nil => simp only [sumOn, List.filter_nil, List.length_nil, scale_zero, zero_add]
  | cons i rest ih =>
      cases hi : select i with
      | false =>
          simp only [sumOn, hi, Bool.false_eq_true, if_false, List.filter_cons, ih]
          exact swap _ _ _
      | true =>
          simp only [sumOn, hi, if_true, List.filter_cons, List.length_cons, ih, scale_succ]
          exact exchange _ _ _ _

variable {D : GNSData} {Index : Type} (P : Family D Index)
  (near : Index → Index → Bool)

theorem neighborLoss_nonneg (i : Index) (schedule : List Index) (x : GNSCompletionSpace D) :
    RCnonneg (P.neighborLoss near i schedule x) := by
  induction schedule generalizing x with
  | nil => exact RCle_refl _
  | cons j rest ih =>
      cases hn : near i j with
      | false =>
          simp only [neighborLoss, hn, Bool.false_eq_true, if_false]
          exact ih (P.op j x)
      | true =>
          simp only [neighborLoss, hn, if_true]
          exact add_nonneg (D.cinner_self_nonneg _) (ih _)

theorem neighborLoss_tail_le (i j : Index) (rest : List Index) (x : GNSCompletionSpace D) :
    RCle (P.neighborLoss near i rest (P.op j x)) (P.neighborLoss near i (j :: rest) x) := by
  cases hn : near i j with
  | false => simp only [neighborLoss, hn, Bool.false_eq_true, if_false]; exact RCle_refl _
  | true =>
      simp only [neighborLoss, hn, if_true]
      exact le_add_of_nonneg_left _ _ (D.cinner_self_nonneg _)

private theorem filter_tail_length {A : Type} (select : A → Bool) (j : A) (rest : List A) :
    (rest.filter select).length ≤ ((j :: rest).filter select).length := by
  cases hn : select j <;> simp only [List.filter_cons, hn, Bool.false_eq_true,
    if_false, if_true, List.length_cons] <;> omega

variable (hcomm : ∀ i j, near i j = false → ∀ x,
  P.op i (P.op j x) = P.op j (P.op i x))

include hcomm in
/-- Any row updated somewhere in the schedule obeys the sparse bound along
the full original trajectory. Earlier losses are nonnegative, not reset. -/
theorem row_bound_of_mem (i : Index) (schedule : List Index)
    (hi : i ∈ schedule) (x : GNSCompletionSpace D) (g : Nat)
    (hrow : (schedule.filter (near i)).length ≤ g) :
    RCle (normSq (P.residual i (P.sweep schedule x)))
      (RCscale (Q'.ofNat g) (P.neighborLoss near i schedule x)) := by
  induction schedule generalizing x with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j rest ih =>
      have ht : (rest.filter (near i)).length ≤ g :=
        Nat.le_trans (filter_tail_length _ _ _) hrow
      have htail := RCscale_mono (Q'.ofNat_nonneg g) (P.neighborLoss_tail_le near i j rest x)
      rcases List.mem_cons.mp hi with heq | hmem
      · subst j
        exact RCle_trans (P.after_own_row_bound near hcomm i rest x g ht) htail
      · exact RCle_trans (ih hmem (P.op j x) ht) htail

/-- Count the TRANSPOSE incidence too: every intermediate step loss is
charged by at most g test rows. This is not a count of the ambient volume. -/
theorem neighborLoss_sum_le (tests schedule : List Index) (x : GNSCompletionSpace D)
    (g : Nat) (hcolumn : ∀ j, j ∈ schedule →
      (tests.filter (fun i => near i j)).length ≤ g) :
    RCle (sumOn tests (fun i => P.neighborLoss near i schedule x))
      (RCscale (Q'.ofNat g) (P.loss schedule x)) := by
  induction schedule generalizing x with
  | nil =>
      have hz : sumOn tests (fun _ => RCzero) = RCzero := by
        clear hcolumn
        induction tests with
        | nil => rfl
        | cons i rest ih => simp only [sumOn, ih, zero_add]
      simp only [neighborLoss, loss, hz, RCscale_RCzero]
      exact RCle_refl _
  | cons j rest ih =>
      simp only [neighborLoss, loss]
      rw [sumOn_step, RCscale_RCadd]
      exact RCadd_le_add
        (RCscale_scalar_mono (ofNat_le_ofNat (hcolumn j List.mem_cons_self))
          (D.cinner_self_nonneg _))
        (ih (P.op j x) (fun k hk => hcolumn k (List.mem_cons_of_mem j hk)))

/-- All residuals are evaluated on the ONE final swept state. -/
def finalEnergy (tests : List Index) (x : GNSCompletionSpace D) : RC :=
  sumOn tests (fun i => normSq (P.residual i x))

include hcomm in
/-- The bounded-incidence energy estimate with no analytic gap input. -/
theorem finalEnergy_le_loss (tests schedule : List Index)
    (hcover : ∀ i, i ∈ tests → i ∈ schedule) (x : GNSCompletionSpace D) (g : Nat)
    (hrow : ∀ i, i ∈ tests → (schedule.filter (near i)).length ≤ g)
    (hcolumn : ∀ j, j ∈ schedule → (tests.filter (fun i => near i j)).length ≤ g) :
    RCle (P.finalEnergy tests (P.sweep schedule x))
      (RCscale (Q'.ofNat g * Q'.ofNat g) (P.loss schedule x)) := by
  have hr := sumOn_mono tests _ _ (fun i hi =>
    P.row_bound_of_mem near hcomm i schedule (hcover i hi) x g (hrow i hi))
  rw [sumOn_scale] at hr
  have hc := RCscale_mono (Q'.ofNat_nonneg g)
    (P.neighborLoss_sum_le near tests schedule x g hcolumn)
  rw [RCscale_RCscale] at hc
  exact RCle_trans hr hc

include hcomm in
/-- Same estimate with the exact Pythagorean loss exposed. -/
theorem finalEnergy_le_norm_loss (tests schedule : List Index)
    (hcover : ∀ i, i ∈ tests → i ∈ schedule) (x : GNSCompletionSpace D) (g : Nat)
    (hrow : ∀ i, i ∈ tests → (schedule.filter (near i)).length ≤ g)
    (hcolumn : ∀ j, j ∈ schedule → (tests.filter (fun i => near i j)).length ≤ g) :
    RCle (P.finalEnergy tests (P.sweep schedule x))
      (RCscale (Q'.ofNat g * Q'.ofNat g)
        (RCsub (normSq x) (normSq (P.sweep schedule x)))) := by
  rw [← P.loss_eq]
  exact P.finalEnergy_le_loss near hcomm tests schedule hcover x g hrow hcolumn

#print axioms sumOn_mono
#print axioms sumOn_scale
#print axioms neighborLoss_nonneg
#print axioms neighborLoss_tail_le
#print axioms row_bound_of_mem
#print axioms neighborLoss_sum_le
#print axioms finalEnergy_le_loss
#print axioms finalEnergy_le_norm_loss

end YMGap.Continuum.GNSProjectionSweep.Family
