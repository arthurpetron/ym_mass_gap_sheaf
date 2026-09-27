/-
# Actual transported neighboring corrections in a completed sweep

After a projection's own update its residual is zero. A later commuting
update transports all existing correction vectors contractively; a neighbor
adds the NEGATIVE actual residual correction. The explicit list below equals
the final residual, with length exactly the neighbor count and energy at
most the sum of the actual neighboring step losses.

Combined with the finite Gram identity, this proves a sparse ROW energy
bound. Summing transpose incidences and useful interacting coercivity are
separate remaining steps; no strict contraction is assumed or claimed.
-/

import YMGap.Continuum.GNSFiniteSumEnergy
import YMGap.Continuum.GNSCommutingSweep

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

private theorem add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv _ _))

private theorem add_reorder (a b c : RC) :
    RCadd (RCadd a b) c = RCadd b (RCadd a c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
      (Q'.add_assoc_eqv _ _ _)))

variable {D : GNSData} {Index : Type} (P : Family D Index)

theorem op_zero (i : Index) : P.op i (embedV D D.zero) = embedV D D.zero := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [P.adjoint, D.cinnerCompl_embedZero_left, D.cinnerCompl_embedZero_left]

theorem op_add (i : Index) (x y : GNSCompletionSpace D) :
    P.op i (D.cAdd x y) = D.cAdd (P.op i x) (P.op i y) := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [P.adjoint, D.cinnerCompl_cAdd_left, D.cinnerCompl_cAdd_left, P.adjoint, P.adjoint]

theorem op_vectorSum (i : Index) (xs : List (GNSCompletionSpace D)) :
    P.op i (vectorSum xs) = vectorSum (xs.map (P.op i)) := by
  induction xs with
  | nil => exact P.op_zero i
  | cons x xs ih =>
      simp only [List.map_cons, vectorSum]
      rw [P.op_add, ih]

private theorem norm_neg (x : GNSCompletionSpace D) : normSq (D.cNeg x) = normSq x := by
  unfold normSq
  rw [D.cinnerCompl_cNeg_left, D.cinnerCompl_comm x (D.cNeg x), D.cinnerCompl_cNeg_left]
  generalize D.cinnerCompl x x = a
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_neg_eqv _))

private theorem neg_add_sub (x y : GNSCompletionSpace D) :
    D.cAdd (D.cNeg y) x = D.cSub x y := by
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro z
  rw [D.cinnerCompl_cAdd_left, D.cinnerCompl_cNeg_left, D.cinnerCompl_cSub_left]
  exact add_comm _ _

theorem energy_map_op (i : Index) (xs : List (GNSCompletionSpace D)) :
    RCle (energy (xs.map (P.op i))) (energy xs) := by
  induction xs with
  | nil => exact RCle_refl _
  | cons x xs ih => exact RCadd_le_add (P.op_norm i x) ih

variable (near : Index → Index → Bool)

/-- Transport existing terms at commuting updates; retain the actual signed
correction at each neighbor. No state is replaced by a free-product state. -/
def correctionWalk (i : Index) : List Index → GNSCompletionSpace D →
    List (GNSCompletionSpace D) → List (GNSCompletionSpace D)
  | [], _, terms => terms
  | j :: rest, x, terms =>
      correctionWalk i rest (P.op j x)
        (if near i j then D.cNeg (P.residual i (P.residual j x)) :: terms
         else terms.map (P.op j))

/-- Sparse sum of step losses along the FULL original trajectory. -/
def neighborLoss (i : Index) : List Index → GNSCompletionSpace D → RC
  | [], _ => RCzero
  | j :: rest, x =>
      if near i j then RCadd (normSq (P.residual j x)) (neighborLoss i rest (P.op j x))
      else neighborLoss i rest (P.op j x)

variable (hcomm : ∀ i j, near i j = false → ∀ x,
  P.op i (P.op j x) = P.op j (P.op i x))

include hcomm in
theorem correctionWalk_eq (i : Index) (schedule : List Index)
    (x : GNSCompletionSpace D) (terms : List (GNSCompletionSpace D))
    (hterms : vectorSum terms = P.residual i x) :
    vectorSum (P.correctionWalk near i schedule x terms) =
      P.residual i (P.sweep schedule x) := by
  induction schedule generalizing x terms with
  | nil => exact hterms
  | cons j rest ih =>
      cases hn : near i j with
      | false =>
          simp only [correctionWalk, hn, Bool.false_eq_true, if_false, sweep]
          apply ih
          rw [← P.op_vectorSum, hterms, P.residual_commute i j (hcomm i j hn)]
      | true =>
          simp only [correctionWalk, hn, if_true, sweep]
          apply ih
          change D.cAdd (D.cNeg (P.residual i (P.residual j x))) (vectorSum terms) = _
          rw [hterms, neg_add_sub, P.residual_update]

theorem correctionWalk_length (i : Index) (schedule : List Index)
    (x : GNSCompletionSpace D) (terms : List (GNSCompletionSpace D)) :
    (P.correctionWalk near i schedule x terms).length =
      terms.length + (schedule.filter (near i)).length := by
  induction schedule generalizing x terms with
  | nil => simp only [correctionWalk, List.filter_nil, List.length_nil, Nat.add_zero]
  | cons j rest ih =>
      cases hn : near i j with
      | false =>
          simp only [correctionWalk, hn, Bool.false_eq_true, if_false, ih,
            List.filter_cons, List.length_map]
      | true =>
          simp only [correctionWalk, hn, if_true, ih, List.filter_cons, List.length_cons]
          omega

theorem correctionWalk_energy (i : Index) (schedule : List Index)
    (x : GNSCompletionSpace D) (terms : List (GNSCompletionSpace D)) :
    RCle (energy (P.correctionWalk near i schedule x terms))
      (RCadd (energy terms) (P.neighborLoss near i schedule x)) := by
  induction schedule generalizing x terms with
  | nil =>
      simp only [correctionWalk, neighborLoss, add_zero]
      exact RCle_refl _
  | cons j rest ih =>
      cases hn : near i j with
      | false =>
          simp only [correctionWalk, neighborLoss, hn, Bool.false_eq_true, if_false]
          exact RCle_trans (ih _ _)
            (RCadd_le_add (P.energy_map_op j terms) (RCle_refl _))
      | true =>
          simp only [correctionWalk, neighborLoss, hn, if_true]
          have h := ih (P.op j x) (D.cNeg (P.residual i (P.residual j x)) :: terms)
          simp only [energy, norm_neg] at h
          have hb := RCadd_le_add
            (RCadd_le_add (P.residual_norm i (P.residual j x)) (RCle_refl (energy terms)))
            (RCle_refl (P.neighborLoss near i rest (P.op j x)))
          rw [add_reorder (normSq (P.residual j x)) (energy terms)
            (P.neighborLoss near i rest (P.op j x))] at hb
          exact RCle_trans h hb

include hcomm in
/-- After its own update, the entire final residual is the constructed
sparse correction list; its coefficient counts only later neighbors. -/
theorem after_own_row_bound (i : Index) (suffix : List Index)
    (x : GNSCompletionSpace D) (bound : Nat)
    (hcount : (suffix.filter (near i)).length ≤ bound) :
    RCle (normSq (P.residual i (P.sweep suffix (P.op i x))))
      (RCscale (Q'.ofNat bound) (P.neighborLoss near i suffix (P.op i x))) := by
  let terms := P.correctionWalk near i suffix (P.op i x) []
  have heq : vectorSum terms = P.residual i (P.sweep suffix (P.op i x)) := by
    apply P.correctionWalk_eq near hcomm
    exact (P.residual_after_own i x).symm
  have hlen : terms.length ≤ bound := by
    rw [correctionWalk_length, List.length_nil, Nat.zero_add]
    exact hcount
  have henergy : RCle (energy terms) (P.neighborLoss near i suffix (P.op i x)) := by
    have h := P.correctionWalk_energy near i suffix (P.op i x) []
    rw [energy, zero_add] at h
    exact h
  rw [← heq]
  exact RCle_trans (norm_vectorSum_le_of_length terms bound hlen)
    (RCscale_mono (CReal.ofNat_le_ofNat (Nat.zero_le bound)) henergy)

#print axioms op_zero
#print axioms op_add
#print axioms op_vectorSum
#print axioms energy_map_op
#print axioms correctionWalk_eq
#print axioms correctionWalk_length
#print axioms correctionWalk_energy
#print axioms after_own_row_bound

end YMGap.Continuum.GNSProjectionSweep.Family
