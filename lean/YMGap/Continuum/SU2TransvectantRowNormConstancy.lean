/-
# Exact tensor-binomial adjointness and raw row-norm recurrence

The coefficient-row identities become a norm identity through the dual
binomial metric on the tensor monomial basis.  This module proves the full
two-dimensional adjoint relation by two finite one-dimensional shifts and
then derives the adjacent raw output-row norm recurrence.
-/

import YMGap.Continuum.SU2TransvectantRowNormRecurrence
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.SU2TransvectantRowNormConstancy

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2TransvectantRowToFullGram
open YMGap.Continuum.SU2TransvectantRowNormRecurrence

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- Exact dual-binomial pairing on a two-factor coefficient array. -/
def tensorBinomPair (m n : Nat) (f g : Nat → Nat → Q') : Q' :=
  finSum (fun i => finSum (fun j =>
    tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1)) (m + 1)

private theorem tensorBinomPair_congr_left (m n : Nat)
    (f f' g : Nat → Nat → Q')
    (h : ∀ i, i < m + 1 → ∀ j, j < n + 1 → f i j ≈ f' i j) :
    tensorBinomPair m n f g ≈ tensorBinomPair m n f' g := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (h i hi j hj)))

private theorem tensorBinomPair_congr_right (m n : Nat)
    (f g g' : Nat → Nat → Q')
    (h : ∀ i, i < m + 1 → ∀ j, j < n + 1 → g i j ≈ g' i j) :
    tensorBinomPair m n f g ≈ tensorBinomPair m n f g' := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (h i hi j hj)))

private theorem tensorBinomPair_add_left (m n : Nat)
    (f h g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => f i j + h i j) g ≈
      tensorBinomPair m n f g + tensorBinomPair m n h g := by
  unfold tensorBinomPair
  have houter := RationalTail.finSum_add
    (fun i => finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1))
    (fun i => finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (h i j * g i j))) (n + 1)) (m + 1)
  refine Q'.eqv_trans _
    (finSum (fun i =>
      finSum (fun j => tvBinomQ n j *
        (tvBinomQ m i * (f i j * g i j))) (n + 1) +
      finSum (fun j => tvBinomQ n j *
        (tvBinomQ m i * (h i j * g i j))) (n + 1)) (m + 1)) _ ?_ houter
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine Q'.eqv_trans _
    (finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j)) +
      tvBinomQ n j * (tvBinomQ m i * (h i j * g i j))) (n + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
    ring_qeqv
  · exact RationalTail.finSum_add _ _ (n + 1)

private theorem tensorBinomPair_add_right (m n : Nat)
    (f g h : Nat → Nat → Q') :
    tensorBinomPair m n f (fun i j => g i j + h i j) ≈
      tensorBinomPair m n f g + tensorBinomPair m n f h := by
  unfold tensorBinomPair
  have houter := RationalTail.finSum_add
    (fun i => finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1))
    (fun i => finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * h i j))) (n + 1)) (m + 1)
  refine Q'.eqv_trans _
    (finSum (fun i =>
      finSum (fun j => tvBinomQ n j *
        (tvBinomQ m i * (f i j * g i j))) (n + 1) +
      finSum (fun j => tvBinomQ n j *
        (tvBinomQ m i * (f i j * h i j))) (n + 1)) (m + 1)) _ ?_ houter
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine Q'.eqv_trans _
    (finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j)) +
      tvBinomQ n j * (tvBinomQ m i * (f i j * h i j))) (n + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
    ring_qeqv
  · exact RationalTail.finSum_add _ _ (n + 1)

private theorem tensorBinomPair_scale_left (m n : Nat) (a : Q')
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => a * f i j) g ≈
      a * tensorBinomPair m n f g := by
  unfold tensorBinomPair
  refine Q'.eqv_trans _
    (finSum (fun i => a * finSum (fun j =>
      tvBinomQ n j * (tvBinomQ m i * (f i j * g i j))) (n + 1)) (m + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
    refine Q'.eqv_trans _
      (finSum (fun j => a * (tvBinomQ n j *
        (tvBinomQ m i * (f i j * g i j)))) (n + 1)) _ ?_ ?_
    · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
      ring_qeqv
    · exact Q'.eqv_symm (const_mul_finSum _ a (n + 1))
  · exact Q'.eqv_symm (const_mul_finSum _ a (m + 1))

private theorem tensorBinomPair_scale_right (m n : Nat) (a : Q')
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n f (fun i j => a * g i j) ≈
      a * tensorBinomPair m n f g := by
  refine Q'.eqv_trans _ (tensorBinomPair m n (fun i j => a * f i j) g) _ ?_
    (tensorBinomPair_scale_left m n a f g)
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  ring_qeqv

private theorem first_shift_adjoint (m n : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => Q'.ofNat i * f (i - 1) j) g ≈
      tensorBinomPair m n f
        (fun i j => Q'.ofNat (m - i) * g (i + 1) j) := by
  unfold tensorBinomPair
  let L : Nat → Nat → Q' := fun i j =>
    tvBinomQ n j *
      (tvBinomQ m i * ((Q'.ofNat i * f (i - 1) j) * g i j))
  let R : Nat → Nat → Q' := fun i j =>
    tvBinomQ n j *
      (tvBinomQ m i * (f i j * (Q'.ofNat (m - i) * g (i + 1) j)))
  have hswapL := RationalTail.finSum_swap L (m + 1) (n + 1)
  have hswapR := RationalTail.finSum_swap R (m + 1) (n + 1)
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun i => L i j) (m + 1)) (n + 1)) _
    (by simpa only [L] using hswapL) ?_
  refine Q'.eqv_trans _
    (finSum (fun j => finSum (fun i => R i j) (m + 1)) (n + 1)) _ ?_
    (Q'.eqv_symm (by simpa only [R] using hswapR))
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  refine Q'.eqv_trans _
    (tvBinomQ n j * finSum (fun i => tvBinomQ m i *
      ((Q'.ofNat i * f (i - 1) j) * g i j)) (m + 1)) _
    (Q'.eqv_symm (const_mul_finSum _ _ _)) ?_
  refine Q'.eqv_trans _
    (tvBinomQ n j * finSum (fun i => tvBinomQ m i *
      (f i j * (Q'.ofNat (m - i) * g (i + 1) j))) (m + 1)) _
    (Q'.mul_eqv_congr_left _ _ _
      (dual_binomial_shift_adjoint m (fun i => f i j) (fun i => g i j))) ?_
  exact const_mul_finSum _ _ _

private theorem second_shift_adjoint (m n : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n (fun i j => Q'.ofNat j * f i (j - 1)) g ≈
      tensorBinomPair m n f
        (fun i j => Q'.ofNat (n - j) * g i (j + 1)) := by
  unfold tensorBinomPair
  refine finSum_eqv_congr_lt _ _ (m + 1) (fun i hi => ?_)
  refine Q'.eqv_trans _
    (finSum (fun j => tvBinomQ m i *
      (tvBinomQ n j * ((Q'.ofNat j * f i (j - 1)) * g i j))) (n + 1)) _ ?_ ?_
  · refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
    ring_qeqv
  refine Q'.eqv_trans _
    (tvBinomQ m i * finSum (fun j => tvBinomQ n j *
      ((Q'.ofNat j * f i (j - 1)) * g i j)) (n + 1)) _
    (Q'.eqv_symm (const_mul_finSum _ _ _)) ?_
  refine Q'.eqv_trans _
    (tvBinomQ m i * finSum (fun j => tvBinomQ n j *
      (f i j * (Q'.ofNat (n - j) * g i (j + 1)))) (n + 1)) _
    (Q'.mul_eqv_congr_left _ _ _
      (dual_binomial_shift_adjoint n (fun j => f i j) (fun j => g i j))) ?_
  refine Q'.eqv_trans _
    (finSum (fun j => tvBinomQ m i *
      (tvBinomQ n j * (f i j *
        (Q'.ofNat (n - j) * g i (j + 1))))) (n + 1)) _
    (const_mul_finSum _ _ _) ?_
  refine finSum_eqv_congr_lt _ _ (n + 1) (fun j hj => ?_)
  ring_qeqv

/-- The total lowering shift on the dual tensor-binomial metric is adjoint to
the total raising shift. -/
theorem tensor_binomial_total_shift_adjoint (m n : Nat)
    (f g : Nat → Nat → Q') :
    tensorBinomPair m n
        (fun i j => Q'.ofNat i * f (i - 1) j +
          Q'.ofNat j * f i (j - 1)) g ≈
      tensorBinomPair m n f
        (fun i j => Q'.ofNat (m - i) * g (i + 1) j +
          Q'.ofNat (n - j) * g i (j + 1)) := by
  refine Q'.eqv_trans _
    (tensorBinomPair m n (fun i j => Q'.ofNat i * f (i - 1) j) g +
      tensorBinomPair m n (fun i j => Q'.ofNat j * f i (j - 1)) g) _
    (tensorBinomPair_add_left _ _ _ _ _) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair m n f
        (fun i j => Q'.ofNat (m - i) * g (i + 1) j) +
      tensorBinomPair m n f
        (fun i j => Q'.ofNat (n - j) * g i (j + 1))) _
    (Q'.add_eqv_congr' (first_shift_adjoint m n f g)
      (second_shift_adjoint m n f g)) ?_
  exact Q'.eqv_symm (tensorBinomPair_add_right _ _ _ _ _)

/-- The unnormalized squared norm of output row `s`. -/
def binaryRawRowNorm (m n k s : Nat) : Q' :=
  let r : Nat → Nat → Q' := fun i j =>
    transvect m n k (tprod (mono i) (mono j)) s
  tensorBinomPair m n r r

/-- Adjacent raw output rows obey the exact representation-theoretic norm
recurrence. -/
theorem binaryRawRowNorm_recurrence (m n k s : Nat)
    (hm : k ≤ m) (hn : k ≤ n) :
    Q'.ofNat (s + 1) * binaryRawRowNorm m n k (s + 1) ≈
      Q'.ofNat (m + n - 2 * k - s) * binaryRawRowNorm m n k s := by
  let f : Nat → Nat → Q' := fun i j =>
    transvect m n k (tprod (mono i) (mono j)) s
  let g : Nat → Nat → Q' := fun i j =>
    transvect m n k (tprod (mono i) (mono j)) (s + 1)
  let LF : Nat → Nat → Q' := fun i j =>
    Q'.ofNat i * f (i - 1) j + Q'.ofNat j * f i (j - 1)
  let EG : Nat → Nat → Q' := fun i j =>
    Q'.ofNat (m - i) * g (i + 1) j +
      Q'.ofNat (n - j) * g i (j + 1)
  have hL : ∀ i, i < m + 1 → ∀ j, j < n + 1 →
      LF i j ≈ Q'.ofNat (s + 1) * g i j := by
    intro i hi j hj
    simpa only [LF, f, g] using
      transvect_row_lowering m n k s i j hm hn (by omega) (by omega)
  have hE : ∀ i, i < m + 1 → ∀ j, j < n + 1 →
      EG i j ≈ Q'.ofNat (m + n - 2 * k - s) * f i j := by
    intro i hi j hj
    simpa only [EG, f, g] using
      transvect_row_raising m n k s i j hm hn (by omega) (by omega)
  have hadj := tensor_binomial_total_shift_adjoint m n f g
  refine Q'.eqv_trans _
    (tensorBinomPair m n (fun i j => Q'.ofNat (s + 1) * g i j) g) _
    (Q'.eqv_symm (tensorBinomPair_scale_left m n _ g g)) ?_
  refine Q'.eqv_trans _ (tensorBinomPair m n LF g) _
    (Q'.eqv_symm (tensorBinomPair_congr_left m n LF
      (fun i j => Q'.ofNat (s + 1) * g i j) g hL)) ?_
  refine Q'.eqv_trans _ (tensorBinomPair m n f EG) _
    (by simpa only [LF, EG] using hadj) ?_
  refine Q'.eqv_trans _
    (tensorBinomPair m n f
      (fun i j => Q'.ofNat (m + n - 2 * k - s) * f i j)) _
    (tensorBinomPair_congr_right m n f EG _ hE) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (m + n - 2 * k - s) * tensorBinomPair m n f f) _
    (tensorBinomPair_scale_right m n _ f f) ?_
  simp only [binaryRawRowNorm, f, g]
  exact Q'.eqv_refl _

end YMGap.Continuum.SU2TransvectantRowNormConstancy

#print axioms YMGap.Continuum.SU2TransvectantRowNormConstancy.tensor_binomial_total_shift_adjoint
#print axioms YMGap.Continuum.SU2TransvectantRowNormConstancy.binaryRawRowNorm_recurrence
