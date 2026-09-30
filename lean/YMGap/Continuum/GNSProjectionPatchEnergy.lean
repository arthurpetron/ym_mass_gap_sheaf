/-
# Exact finite-patch energy accounting for completed projection residuals

Every patch keeps an arbitrary sublist of one original test list.  The
aggregate square is an exact signed Gram sum weighted by the number of
patches containing both indices; the aggregate diagonal is the same
Dirichlet energy weighted by single-index incidence.  No patch spectral
estimate or positivity of neighboring cross terms is assumed.
-/

import YMGap.Continuum.GNSProjectionSignedEnergy

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient

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

private theorem rc_scale_zero (a : RC) : RCscale (Q'.ofNat 0) a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.zero_mul_eqv _))

private theorem rc_scale_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd a (RCscale (Q'.ofNat n) a) := by
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
  | cons a rest ih => simp only [sumOn, ih, rc_zero_add]

private theorem sumOn_ext {A : Type} (xs : List A) (f g : A → RC)
    (h : ∀ a, a ∈ xs → f a = g a) : sumOn xs f = sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp only [sumOn]
      rw [h a List.mem_cons_self]
      exact congrArg (fun v => RCadd (g a) v)
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem sumOn_filter {A : Type} (xs : List A) (select : A → Bool)
    (f : A → RC) :
    sumOn (xs.filter select) f =
      sumOn xs (fun a => if select a then f a else RCzero) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      cases h : select a with
      | false =>
          simp only [List.filter_cons, h, Bool.false_eq_true,
            if_false, sumOn, ih, rc_zero_add]
      | true =>
          simp only [List.filter_cons, h, if_true, sumOn, ih]

private theorem sumOn_comm {A B : Type} (xs : List A) (ys : List B)
    (f : A → B → RC) :
    sumOn xs (fun a => sumOn ys (fun b => f a b)) =
      sumOn ys (fun b => sumOn xs (fun a => f a b)) := by
  induction xs with
  | nil => simp only [sumOn, sumOn_zero]
  | cons a rest ih =>
      change RCadd (sumOn ys (fun b => f a b))
          (sumOn rest (fun u => sumOn ys (fun b => f u b))) =
        sumOn ys (fun b => RCadd (f a b) (sumOn rest (fun u => f u b)))
      rw [ih]
      exact (sumOn_add ys (fun b => f a b)
        (fun b => sumOn rest (fun u => f u b))).symm

private theorem sumOn_selector_count {A : Type} (xs : List A)
    (select : A → Bool) (v : RC) :
    sumOn xs (fun a => if select a then v else RCzero) =
      RCscale (Q'.ofNat (xs.filter select).length) v := by
  induction xs with
  | nil => exact (rc_scale_zero v).symm
  | cons a rest ih =>
      cases h : select a with
      | false =>
          simp only [sumOn, h, Bool.false_eq_true, if_false,
            List.filter_cons, rc_zero_add]
          exact ih
      | true =>
          simp only [sumOn, h, if_true, List.filter_cons, List.length_cons]
          rw [ih, rc_scale_succ]

private theorem double_filter {Index : Type} (tests : List Index)
    (keep : Index → Bool) (g : Index → Index → RC) :
    sumOn (tests.filter keep)
      (fun i => sumOn (tests.filter keep) (fun j => g i j)) =
    sumOn tests (fun i => sumOn tests (fun j =>
      if keep i && keep j then g i j else RCzero)) := by
  rw [sumOn_filter]
  apply sumOn_ext
  intro i _
  cases hi : keep i with
  | false =>
      simp only [Bool.false_and, Bool.false_eq_true, if_false]
      exact (sumOn_zero tests).symm
  | true =>
      simp only [Bool.true_and, if_true]
      exact sumOn_filter tests keep (fun j => g i j)

variable {D : GNSData} {Index Patch : Type} (P : Family D Index)

/-- Number of patches retaining both test indices, with list multiplicity. -/
def jointCount (patches : List Patch) (keep : Patch → Index → Bool)
    (i j : Index) : Nat :=
  (patches.filter (fun a => keep a i && keep a j)).length

def patchSquareSum (tests : List Index) (patches : List Patch)
    (keep : Patch → Index → Bool) (x : GNSCompletionSpace D) : RC :=
  sumOn patches (fun a => normSq (P.residualSum (tests.filter (keep a)) x))

def patchEnergySum (tests : List Index) (patches : List Patch)
    (keep : Patch → Index → Bool) (x : GNSCompletionSpace D) : RC :=
  sumOn patches (fun a => P.finalEnergy (tests.filter (keep a)) x)

private theorem patch_square_pairing (tests : List Index)
    (x : GNSCompletionSpace D) :
    normSq (P.residualSum tests x) =
      sumOn tests (fun i => sumOn tests (fun j =>
        D.cinnerCompl (P.residual i x) (P.residual j x))) := by
  unfold normSq
  rw [P.residualSum_pairing]
  apply congrArg (sumOn tests)
  funext i
  exact P.residualSum_pairing_right tests (P.residual i x) x

/-- Exact ordered Gram expansion of every finite patch square.  Pair signs
are retained; no remote or neighboring term is discarded. -/
theorem patchSquareSum_expansion (tests : List Index) (patches : List Patch)
    (keep : Patch → Index → Bool) (x : GNSCompletionSpace D) :
    P.patchSquareSum tests patches keep x =
      sumOn tests (fun i => sumOn tests (fun j =>
        RCscale (Q'.ofNat (jointCount patches keep i j))
          (D.cinnerCompl (P.residual i x) (P.residual j x)))) := by
  unfold patchSquareSum
  have hpatch (a : Patch) :
      normSq (P.residualSum (tests.filter (keep a)) x) =
      sumOn tests (fun i => sumOn tests (fun j =>
        if keep a i && keep a j then
          D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero)) := by
    rw [P.patch_square_pairing]
    exact double_filter tests (keep a)
      (fun i j => D.cinnerCompl (P.residual i x) (P.residual j x))
  rw [sumOn_ext patches _ _ (fun a _ => hpatch a)]
  rw [sumOn_comm patches tests]
  apply congrArg (sumOn tests)
  funext i
  rw [sumOn_comm patches tests]
  apply congrArg (sumOn tests)
  funext j
  exact sumOn_selector_count patches (fun a => keep a i && keep a j)
    (D.cinnerCompl (P.residual i x) (P.residual j x))

/-- Exact diagonal patch incidence, including varying boundary degrees. -/
theorem patchEnergySum_expansion (tests : List Index) (patches : List Patch)
    (keep : Patch → Index → Bool) (x : GNSCompletionSpace D) :
    P.patchEnergySum tests patches keep x =
      sumOn tests (fun i => RCscale (Q'.ofNat (jointCount patches keep i i))
        (normSq (P.residual i x))) := by
  unfold patchEnergySum finalEnergy
  rw [sumOn_ext patches _ _ (fun a _ =>
    sumOn_filter tests (keep a) (fun i => normSq (P.residual i x)))]
  rw [sumOn_comm patches tests]
  apply congrArg (sumOn tests)
  funext i
  have hsame (a : Patch) : (keep a i && keep a i) = keep a i := by
    cases keep a i <;> rfl
  rw [sumOn_ext patches
    (fun a => if keep a i then normSq (P.residual i x) else RCzero)
    (fun a => if keep a i && keep a i then normSq (P.residual i x) else RCzero)
    (fun a _ => by dsimp only; rw [hsame a])]
  exact sumOn_selector_count patches (fun a => keep a i && keep a i)
    (normSq (P.residual i x))

/-- The patch diagonal is bounded by the maximum incidence, with no
assumption about signs of distinct residual pairings. -/
theorem patchEnergySum_le_degree (tests : List Index) (patches : List Patch)
    (keep : Patch → Index → Bool) (x : GNSCompletionSpace D)
    (degree : Nat)
    (hdegree : ∀ i, i ∈ tests → jointCount patches keep i i ≤ degree) :
    RCle (P.patchEnergySum tests patches keep x)
      (RCscale (Q'.ofNat degree) (P.finalEnergy tests x)) := by
  rw [P.patchEnergySum_expansion]
  have h := sumOn_mono tests
    (fun i => RCscale (Q'.ofNat (jointCount patches keep i i))
      (normSq (P.residual i x)))
    (fun i => RCscale (Q'.ofNat degree) (normSq (P.residual i x)))
    (fun i hi => RCscale_scalar_mono (ofNat_le_ofNat (hdegree i hi))
      (D.cinner_self_nonneg _))
  rw [sumOn_scale] at h
  exact h

private theorem sumOn_indicator_absent {A : Type} [DecidableEq A]
    (xs : List A) (i : A) (hi : i ∉ xs) (v : RC) :
    sumOn xs (fun j => if i = j then v else RCzero) = RCzero := by
  induction xs with
  | nil => rfl
  | cons j rest ih =>
      have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
      have hr : i ∉ rest := fun h => hi (List.mem_cons_of_mem j h)
      simp only [sumOn, if_neg hij, ih hr, rc_zero_add]

private theorem sumOn_indicator {A : Type} [DecidableEq A]
    (xs : List A) (hs : xs.Nodup) (i : A) (hi : i ∈ xs) (v : RC) :
    sumOn xs (fun j => if i = j then v else RCzero) = v := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j rest ih =>
      have hn := List.nodup_cons.mp hs
      by_cases hij : i = j
      · subst i
        simp only [sumOn, if_true,
          sumOn_indicator_absent rest j hn.1 v, rc_add_zero]
      · have hr : i ∈ rest := (List.mem_cons.mp hi).resolve_left hij
        simp only [sumOn, if_neg hij, ih hn.2 hr, rc_zero_add]

/-- If every distinct neighboring ordered pair shares exactly one patch
and every distinct remote pair shares none, the aggregate square is the
aggregate diagonal plus the EXISTING signed neighboring cross energy.
The boundary-dependent diagonal multiplicity is left untouched. -/
theorem patchSquareSum_eq_energy_add_cross [DecidableEq Index]
    (tests : List Index) (hs : tests.Nodup) (patches : List Patch)
    (keep : Patch → Index → Bool) (near : Index → Index → Bool)
    (x : GNSCompletionSpace D)
    (hoff : ∀ i j, i ∈ tests → j ∈ tests → i ≠ j →
      jointCount patches keep i j = if near i j then 1 else 0) :
    P.patchSquareSum tests patches keep x =
      RCadd (P.patchEnergySum tests patches keep x)
        (P.neighboringCross near tests x) := by
  rw [P.patchSquareSum_expansion, P.patchEnergySum_expansion]
  unfold neighboringCross
  have hrow (i : Index) (hi : i ∈ tests) :
      sumOn tests (fun j => RCscale (Q'.ofNat (jointCount patches keep i j))
        (D.cinnerCompl (P.residual i x) (P.residual j x))) =
      RCadd (RCscale (Q'.ofNat (jointCount patches keep i i))
        (normSq (P.residual i x)))
        (sumOn tests (fun j => if i = j then RCzero else
          if near i j then D.cinnerCompl (P.residual i x)
            (P.residual j x) else RCzero)) := by
    have hp (j : Index) (hj : j ∈ tests) :
        RCscale (Q'.ofNat (jointCount patches keep i j))
          (D.cinnerCompl (P.residual i x) (P.residual j x)) =
        RCadd (if i = j then RCscale (Q'.ofNat (jointCount patches keep i i))
          (normSq (P.residual i x)) else RCzero)
          (if i = j then RCzero else if near i j then
            D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero) := by
      by_cases hij : i = j
      · subst j
        simp only [if_true, normSq, rc_add_zero]
      · rw [hoff i j hi hj hij]
        cases hnear : near i j with
        | false =>
            simp only [hij, if_false, Bool.false_eq_true,
              rc_scale_zero, rc_zero_add]
        | true =>
            simp only [hij, if_false, if_true, rc_zero_add]
            exact RCscale_one _
    rw [sumOn_ext tests _ _ hp, sumOn_add]
    rw [sumOn_indicator tests hs i hi
      (RCscale (Q'.ofNat (jointCount patches keep i i))
        (normSq (P.residual i x)))]
  rw [sumOn_ext tests _ _ hrow, sumOn_add]


#print axioms jointCount
#print axioms patchSquareSum
#print axioms patchEnergySum
#print axioms patchSquareSum_expansion
#print axioms patchEnergySum_expansion
#print axioms patchEnergySum_le_degree
#print axioms patchSquareSum_eq_energy_add_cross

end YMGap.Continuum.GNSProjectionSweep.Family
