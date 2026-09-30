/-
# Directed finite pair error budgets in the completed real quotient

This module sums two-sided endpoint-energy error bounds over an arbitrary
finite directed relation. Separate row and column incidence bounds charge
each endpoint at most `degree` times; no symmetry or pairing structure is
assumed for the pair fields.
-/

import YMGap.Continuum.GNSProjectionNeighborLowerBound
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.RCDirectedPairError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.RCSignedPairBudget (neg_mono)

/-- Sum a directed pair field only over selected entries of a finite list. -/
def pairSum {A : Type} (xs : List A) (edge : A → A → Bool)
    (a : A → A → RC) : RC :=
  sumOn xs (fun i => sumOn xs (fun j => if edge i j then a i j else RCzero))

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

private theorem rc_scale_zero (a : RC) :
    RCscale (Q'.ofNat 0) a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem rc_scale_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n + 1)) a =
      RCadd a (RCscale (Q'.ofNat n) a) := by
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

private theorem sumOn_sub {A : Type} (xs : List A) (f g : A → RC) :
    sumOn xs (fun i => RCsub (f i) (g i)) =
      RCsub (sumOn xs f) (sumOn xs g) := by
  change sumOn xs (fun i => RCadd (f i) (RCneg (g i))) = _
  rw [sumOn_add, sumOn_neg]
  rfl

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

private theorem double_scale (degree : Nat) (r : Q') (a : RC) :
    RCadd (RCscale (Q'.ofNat degree) (RCscale r a))
      (RCscale (Q'.ofNat degree) (RCscale r a)) =
        RCscale ((2 : Q') * Q'.ofNat degree * r) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
      (by decide)
      (fun | 0 => Q'.ofNat degree | 1 => r | _ => A.approx n)))

private theorem pairSum_sub {A : Type} (xs : List A) (edge : A → A → Bool)
    (a b : A → A → RC) :
    RCsub (pairSum xs edge a) (pairSum xs edge b) =
      pairSum xs edge (fun i j => RCsub (a i j) (b i j)) := by
  unfold pairSum
  rw [← sumOn_sub]
  apply congrArg (sumOn xs)
  funext i
  rw [← sumOn_sub]
  apply congrArg (sumOn xs)
  funext j
  cases h : edge i j with
  | false =>
      simp only [Bool.false_eq_true, if_false, RCsub, rc_neg_zero, rc_zero_add]
  | true => simp only [if_true]

private theorem pairSum_neg {A : Type} (xs : List A)
    (edge : A → A → Bool) (a : A → A → RC) :
    pairSum xs edge (fun i j => RCneg (a i j)) =
      RCneg (pairSum xs edge a) := by
  unfold pairSum
  have hinner (i : A) :
      sumOn xs (fun j => if edge i j then RCneg (a i j) else RCzero) =
        RCneg (sumOn xs (fun j => if edge i j then a i j else RCzero)) := by
    have hf : (fun j => if edge i j then RCneg (a i j) else RCzero) =
        (fun j => RCneg (if edge i j then a i j else RCzero)) := by
      funext j
      cases edge i j <;> simp [rc_neg_zero]
    rw [hf, sumOn_neg]
  have hf : (fun i => sumOn xs
      (fun j => if edge i j then RCneg (a i j) else RCzero)) =
      (fun i => RCneg (sumOn xs
        (fun j => if edge i j then a i j else RCzero))) := by
    funext i
    exact hinner i
  rw [hf, sumOn_neg]

/-! The selected endpoint-energy charge is at most the two incidence budgets. -/

/-- Each selected directed pair charges its two endpoints once. Row and column
incidence bounds therefore give `2 * degree * r` times the total endpoint
energy, without any symmetry assumption on `edge`. -/
theorem endpoint_charge_bound {A : Type} (xs : List A)
    (edge : A → A → Bool) (E : A → RC) (degree : Nat) (r : Q')
    (hr : (0 : Q') ≤ r)
    (hE : ∀ i, i ∈ xs → RCnonneg (E i))
    (hrow : ∀ i, i ∈ xs → (xs.filter (edge i)).length ≤ degree)
    (hcolumn : ∀ j, j ∈ xs → (xs.filter (fun i => edge i j)).length ≤ degree) :
    RCle
      (pairSum xs edge (fun i j => RCscale r (RCadd (E i) (E j))))
      (RCscale ((2 : Q') * Q'.ofNat degree * r) (sumOn xs E)) := by
  let first : A → A → RC := fun i j =>
    if edge i j then RCscale r (E i) else RCzero
  let second : A → A → RC := fun i j =>
    if edge i j then RCscale r (E j) else RCzero
  have heE (i : A) (hi : i ∈ xs) : RCnonneg (RCscale r (E i)) := by
    change RCle RCzero (RCscale r (E i))
    rw [← RCscale_RCzero r]
    exact RCscale_mono hr (hE i hi)
  have hfirst (i : A) (hi : i ∈ xs) :
      RCle (sumOn xs (first i))
        (RCscale (Q'.ofNat degree) (RCscale r (E i))) := by
    exact selected_le xs (edge i) _ (heE i hi) degree (hrow i hi)
  have hsecond (j : A) (hj : j ∈ xs) :
      RCle (sumOn xs (fun i => second i j))
        (RCscale (Q'.ofNat degree) (RCscale r (E j))) := by
    exact selected_le xs (fun i => edge i j) _ (heE j hj) degree (hcolumn j hj)
  have hfirstSum :
      RCle (sumOn xs (fun i => sumOn xs (first i)))
        (RCscale (Q'.ofNat degree) (RCscale r (sumOn xs E))) := by
    have h := sumOn_mono xs _ _ hfirst
    rw [sumOn_scale, sumOn_scale] at h
    exact h
  have hsecondSum :
      RCle (sumOn xs (fun i => sumOn xs (second i)))
        (RCscale (Q'.ofNat degree) (RCscale r (sumOn xs E))) := by
    rw [sumOn_swap xs xs second]
    have h := sumOn_mono xs _ _ hsecond
    rw [sumOn_scale, sumOn_scale] at h
    exact h
  have hsplit (i j : A) :
      (if edge i j then RCscale r (RCadd (E i) (E j)) else RCzero) =
        RCadd (first i j) (second i j) := by
    cases he : edge i j <;> simp [first, second, he, RCscale_RCadd, rc_zero_add]
  have htotal :
      pairSum xs edge (fun i j => RCscale r (RCadd (E i) (E j))) =
        RCadd (sumOn xs (fun i => sumOn xs (first i)))
          (sumOn xs (fun i => sumOn xs (second i))) := by
    unfold pairSum
    calc
      sumOn xs (fun i => sumOn xs
          (fun j => if edge i j then RCscale r (RCadd (E i) (E j)) else RCzero)) =
        sumOn xs (fun i => sumOn xs (fun j => RCadd (first i j) (second i j))) := by
          apply congrArg (sumOn xs)
          funext i
          apply congrArg (sumOn xs)
          funext j
          exact hsplit i j
      _ = sumOn xs (fun i => RCadd (sumOn xs (first i)) (sumOn xs (second i))) := by
          apply congrArg (sumOn xs)
          funext i
          exact sumOn_add xs (first i) (second i)
      _ = _ := sumOn_add xs _ _
  rw [htotal]
  exact RCle_trans (RCadd_le_add hfirstSum hsecondSum)
    (by rw [double_scale]; exact RCle_refl _)

/-- Summed pair fields differ by at most a charge to both endpoints of each
selected directed edge. The two pointwise bounds are explicit and no sign or
symmetry assumption is made about either pair field. -/
theorem pairSum_error_bounds {A : Type} (xs : List A)
    (edge : A → A → Bool) (E : A → RC) (a b : A → A → RC)
    (degree : Nat) (r : Q')
    (hr : (0 : Q') ≤ r)
    (hE : ∀ i, i ∈ xs → RCnonneg (E i))
    (hrow : ∀ i, i ∈ xs → (xs.filter (edge i)).length ≤ degree)
    (hcolumn : ∀ j, j ∈ xs → (xs.filter (fun i => edge i j)).length ≤ degree)
    (hpair : ∀ i j, i ∈ xs → j ∈ xs → edge i j = true →
      RCle (RCneg (RCscale r (RCadd (E i) (E j))))
        (RCsub (a i j) (b i j)) ∧
      RCle (RCsub (a i j) (b i j))
        (RCscale r (RCadd (E i) (E j)))) :
    RCle
      (RCneg (RCscale ((2 : Q') * Q'.ofNat degree * r) (sumOn xs E)))
      (RCsub (pairSum xs edge a) (pairSum xs edge b)) ∧
    RCle
      (RCsub (pairSum xs edge a) (pairSum xs edge b))
      (RCscale ((2 : Q') * Q'.ofNat degree * r) (sumOn xs E)) := by
  let charge : A → A → RC := fun i j => RCscale r (RCadd (E i) (E j))
  let budget := RCscale ((2 : Q') * Q'.ofNat degree * r) (sumOn xs E)
  have hcharge : RCle (pairSum xs edge charge) budget := by
    exact endpoint_charge_bound xs edge E degree r hr hE hrow hcolumn
  have hlocalLower (i j : A) (hi : i ∈ xs) (hj : j ∈ xs) :
      RCle (if edge i j then RCneg (charge i j) else RCzero)
        (if edge i j then RCsub (a i j) (b i j) else RCzero) := by
    cases he : edge i j with
    | false => exact RCle_refl _
    | true => simpa [charge, he] using (hpair i j hi hj he).1
  have hlocalUpper (i j : A) (hi : i ∈ xs) (hj : j ∈ xs) :
      RCle (if edge i j then RCsub (a i j) (b i j) else RCzero)
        (if edge i j then charge i j else RCzero) := by
    cases he : edge i j with
    | false => exact RCle_refl _
    | true => simpa [charge, he] using (hpair i j hi hj he).2
  have hsumLower :
      RCle (RCneg (pairSum xs edge charge))
        (pairSum xs edge (fun i j => RCsub (a i j) (b i j))) := by
    have h := sumOn_mono xs _ _ (fun i hi =>
      sumOn_mono xs _ _ (fun j hj => hlocalLower i j hi hj))
    change RCle (pairSum xs edge (fun i j => RCneg (charge i j))) _ at h
    rw [pairSum_neg] at h
    exact h
  have hsumUpper :
      RCle (pairSum xs edge (fun i j => RCsub (a i j) (b i j)))
        (pairSum xs edge charge) := by
    exact sumOn_mono xs _ _ (fun i hi =>
      sumOn_mono xs _ _ (fun j hj => hlocalUpper i j hi hj))
  constructor
  · rw [pairSum_sub]
    exact RCle_trans (neg_mono hcharge) hsumLower
  · rw [pairSum_sub]
    exact RCle_trans hsumUpper hcharge

#print axioms pairSum
#print axioms endpoint_charge_bound
#print axioms pairSum_error_bounds

end YMGap.Continuum.RCDirectedPairError
