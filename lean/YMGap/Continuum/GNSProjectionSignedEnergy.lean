/-
# The signed neighborhood part of the actual residual-sum square

For a finite family of completed orthogonal projections, form Hx=sum_i R_i x.
Its norm square is exactly the signed neighborhood Gram sum plus a sum of
nonnegative composed-residual squares at commuting nonneighbors. Diagonal
terms are retained in the neighborhood sum when the relation is reflexive.
No smallness of the remaining signed terms or spectral gap is assumed.
-/

import YMGap.Continuum.GNSProjectionResidualPair
import YMGap.Continuum.GNSProjectionSweepEnergy

namespace YMGap.Continuum.GNSProjectionSweep.Family

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSFiniteSumEnergy

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem add_exchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn d ?_
  intro E
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (by decide) (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => E.approx n)))

theorem sumOn_add {A : Type} (xs : List A) (f g : A → RC) :
    sumOn xs (fun i => RCadd (f i) (g i)) = RCadd (sumOn xs f) (sumOn xs g) := by
  induction xs with
  | nil => exact (zero_add RCzero).symm
  | cons i rest ih => simp only [sumOn, ih]; exact add_exchange _ _ _ _

theorem sumOn_nonnegative {A : Type} (xs : List A) (f : A → RC)
    (h : ∀ i, i ∈ xs → RCnonneg (f i)) : RCnonneg (sumOn xs f) := by
  induction xs with
  | nil => exact RCle_refl _
  | cons i rest ih =>
      have hb := RCadd_le_add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))
      rw [zero_add] at hb
      exact hb

private theorem sumOn_indicator_absent {A : Type} [DecidableEq A]
    (xs : List A) (i : A) (hi : i ∉ xs) (a : RC) :
    sumOn xs (fun j => if i = j then a else RCzero) = RCzero := by
  induction xs with
  | nil => rfl
  | cons j rest ih =>
      have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
      have hr : i ∉ rest := fun h => hi (List.mem_cons_of_mem j h)
      simp only [sumOn, if_neg hij, ih hr, zero_add]

private theorem sumOn_indicator {A : Type} [DecidableEq A]
    (xs : List A) (hs : xs.Nodup) (i : A) (hi : i ∈ xs) (a : RC) :
    sumOn xs (fun j => if i = j then a else RCzero) = a := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil hi)
  | cons j rest ih =>
      have hn := List.nodup_cons.mp hs
      by_cases hij : i = j
      · subst i
        simp only [sumOn, if_true, sumOn_indicator_absent rest j hn.1 a, add_zero]
      · have hr : i ∈ rest := (List.mem_cons.mp hi).resolve_left hij
        simp only [sumOn, if_neg hij, ih hn.2 hr, zero_add]

variable {D : GNSData} {Index : Type} (P : Family D Index)

/-- A constructed operator on the same completion, with list multiplicity. -/
def residualSum (tests : List Index) (x : GNSCompletionSpace D) : GNSCompletionSpace D :=
  vectorSum (tests.map (fun i => P.residual i x))

theorem residualSum_pairing (tests : List Index) (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.residualSum tests x) y =
      sumOn tests (fun i => D.cinnerCompl (P.residual i x) y) := by
  induction tests with
  | nil => exact D.cinnerCompl_embedZero_left y
  | cons i rest ih =>
      change D.cinnerCompl (D.cAdd (P.residual i x) (P.residualSum rest x)) y = _
      rw [D.cinnerCompl_cAdd_left, ih]
      rfl

theorem residualSum_pairing_right (tests : List Index) (x y : GNSCompletionSpace D) :
    D.cinnerCompl x (P.residualSum tests y) =
      sumOn tests (fun j => D.cinnerCompl x (P.residual j y)) := by
  induction tests with
  | nil => exact D.cinnerCompl_embedZero_right x
  | cons j rest ih =>
      change D.cinnerCompl x (D.cAdd (P.residual j y) (P.residualSum rest y)) = _
      rw [D.cinnerCompl_cAdd_right, ih]
      rfl

theorem residualSum_adjoint (tests : List Index) (x y : GNSCompletionSpace D) :
    D.cinnerCompl (P.residualSum tests x) y = D.cinnerCompl x (P.residualSum tests y) := by
  rw [P.residualSum_pairing, P.residualSum_pairing_right]
  apply congrArg (sumOn tests)
  funext i
  exact P.residual_adjoint i x y

/-- The quadratic form of the actual residual sum is exactly Dirichlet energy. -/
theorem residualSum_self_pairing (tests : List Index) (x : GNSCompletionSpace D) :
    D.cinnerCompl (P.residualSum tests x) x = P.finalEnergy tests x := by
  rw [P.residualSum_pairing]
  apply congrArg (sumOn tests)
  funext i
  change D.cinnerCompl (P.residual i x) x =
    D.cinnerCompl (P.residual i x) (P.residual i x)
  rw [P.residual_adjoint i x x, P.residual_adjoint i x (P.residual i x), P.residual_idem]

variable (near : Index → Index → Bool)

/-- Ordered neighborhood pairs, including their signed cross terms and any
diagonal selected by `near`. No absolute values or replacement norms. -/
def neighborhoodGram (tests : List Index) (x : GNSCompletionSpace D) : RC :=
  sumOn tests (fun i => sumOn tests (fun j =>
    if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero))

/-- The remote part is represented by actual nonnegative vector squares. -/
def remoteSquares (tests : List Index) (x : GNSCompletionSpace D) : RC :=
  sumOn tests (fun i => sumOn tests (fun j =>
    if near i j then RCzero else normSq (P.residual i (P.residual j x))))

/-- Ordered distinct neighboring cross terms; their signs are preserved. -/
def neighboringCross [DecidableEq Index] (tests : List Index) (x : GNSCompletionSpace D) : RC :=
  sumOn tests (fun i => sumOn tests (fun j =>
    if i = j then RCzero else
      if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero))

/-- The diagonal of a duplicate-free, reflexive neighborhood Gram matrix is
exactly the existing conditional Dirichlet energy, not a substitute form. -/
theorem neighborhoodGram_diagonal [DecidableEq Index]
    (href : ∀ i, near i i = true) (tests : List Index) (hs : tests.Nodup)
    (x : GNSCompletionSpace D) :
    P.neighborhoodGram near tests x =
      RCadd (P.finalEnergy tests x) (P.neighboringCross near tests x) := by
  have hrow (i : Index) (hi : i ∈ tests) :
      sumOn tests (fun j => if near i j then
        D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero) =
      RCadd (normSq (P.residual i x)) (sumOn tests (fun j =>
        if i = j then RCzero else
          if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero)) := by
    have hf : (fun j => if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero) =
        (fun j => RCadd (if i = j then normSq (P.residual i x) else RCzero)
          (if i = j then RCzero else
            if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero)) := by
      funext j
      by_cases hij : i = j
      · subst j
        simp only [href, if_true, add_zero, normSq]
      · simp only [if_neg hij, zero_add]
    rw [hf, sumOn_add, sumOn_indicator tests hs i hi]
  have sum_congr {A : Type} (xs : List A) (f g : A → RC)
      (h : ∀ i, i ∈ xs → f i = g i) : sumOn xs f = sumOn xs g := by
    induction xs with
    | nil => rfl
    | cons i rest ih =>
        simp only [sumOn, h i List.mem_cons_self,
          ih (fun j hj => h j (List.mem_cons_of_mem i hj))]
  unfold neighborhoodGram
  rw [sum_congr tests _ _ hrow, sumOn_add]
  rfl

theorem remoteSquares_nonnegative (tests : List Index) (x : GNSCompletionSpace D) :
    RCnonneg (P.remoteSquares near tests x) := by
  apply sumOn_nonnegative
  intro i _
  apply sumOn_nonnegative
  intro j _
  cases near i j <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact D.cinner_self_nonneg _
  · exact RCle_refl _

variable (hcomm : ∀ i j, near i j = false → ∀ x,
  P.op i (P.op j x) = P.op j (P.op i x))

include hcomm in
/-- Exact signed local/positive remote decomposition, for every completed
input. The diagonal is not lost when the neighborhood relation is reflexive. -/
theorem residualSum_square_decomposition (tests : List Index) (x : GNSCompletionSpace D) :
    normSq (P.residualSum tests x) =
      RCadd (P.neighborhoodGram near tests x) (P.remoteSquares near tests x) := by
  unfold normSq
  rw [P.residualSum_pairing]
  simp only [P.residualSum_pairing_right]
  have hpair (i j : Index) :
      D.cinnerCompl (P.residual i x) (P.residual j x) =
      RCadd (if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero)
        (if near i j then RCzero else normSq (P.residual i (P.residual j x))) := by
    cases h : near i j with
    | true => simp only [if_true, add_zero]
    | false =>
        simp only [Bool.false_eq_true, if_false, zero_add]
        exact P.commuting_residual_pairing_eq_normSq i j (hcomm i j h) x
  refine Eq.trans (b := sumOn tests (fun i => sumOn tests (fun j =>
    RCadd (if near i j then D.cinnerCompl (P.residual i x) (P.residual j x) else RCzero)
      (if near i j then RCzero else normSq (P.residual i (P.residual j x)))))) ?_ ?_
  · apply congrArg (sumOn tests)
    funext i
    apply congrArg (sumOn tests)
    funext j
    exact hpair i j
  · simp only [sumOn_add]
    rfl

include hcomm in
/-- Only the signed neighborhood part needs a new analytic lower estimate. -/
theorem neighborhoodGram_le_residualSum_square (tests : List Index) (x : GNSCompletionSpace D) :
    RCle (P.neighborhoodGram near tests x) (normSq (P.residualSum tests x)) := by
  rw [P.residualSum_square_decomposition near hcomm]
  have h := RCadd_le_add (RCle_refl (P.neighborhoodGram near tests x))
    (P.remoteSquares_nonnegative near tests x)
  rw [add_zero] at h
  exact h

#print axioms sumOn_add
#print axioms sumOn_nonnegative
#print axioms residualSum_pairing
#print axioms residualSum_pairing_right
#print axioms residualSum_adjoint
#print axioms residualSum_self_pairing
#print axioms neighborhoodGram_diagonal
#print axioms remoteSquares_nonnegative
#print axioms residualSum_square_decomposition
#print axioms neighborhoodGram_le_residualSum_square

end YMGap.Continuum.GNSProjectionSweep.Family
